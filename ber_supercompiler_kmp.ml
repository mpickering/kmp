(* To be run with BER MetaOCaml 4.01.0.  The easiest way to get it is
   through opam.  Do

     $ opam switch 4.01.0+BER

   and follow the instruction it prints.  Start a toplevel by invoking

     $ metaocaml

   and load this file by typing

     # use "ber_supercompiler_kmp.ml";;

   including the # and the ;; part.

   Don't hesitate to email me if this doesn't work or if you have any
   questions.  General information about MetaOCaml, including a
   detailed tutorial, can be found on Oleg Kiselyov's website:
   http://okmij.org/ftp/ML/MetaOCaml.html

*)

(* This file is distributed under the terms of the Q Public License
   version 1.0, a copy of which is included at the very end of this
   file.  MetaOCaml source code that uses run must be QPL'ed because
   the staging runtime includes the OCaml compiler which is QPL'ed.
   (Although off-line generated code (i.e. you print the generated
   code to a file instead of running it directly) doesn't have to be
   QPL'ed.)  *)

(* This file demonstrates that staging can express the information
   propagation in a supercompiler, following the style of Sorensen et
   al., by updating the static portion of partially static data
   structures in-place to reflect conditional assumptions.  The
   technique developed here is useful for writing self-optimizing
   libraries; such libraries are more robust and analyzable when
   expressed within a clearly defined language rather than by relying
   on compiler optimizations and ad-hoc pragmas.

   This case study is partly meant to remedy the present situation in
   which the literature has a wealth of multi-stage type systems but a
   dearth of documentation on practical multi-stage programming
   techniques.  This study in particular shows that staging with
   effects can do more than partial evaluation, which adds to the
   motivation and recent interest in effectful multi-stage type
   systems.


   [Implementation Notes]

   This file implements the KMP string-search algorithm, but for
   convenience it works on char list instead of string.  In comments I
   use "this syntax" for writing char list literals.  You might find
     str_to_list : string -> char list
   at the end of this file handy when trying out the search algorithm
   interactively.

   The redundant (*  *) below some comments are inserted to prevent
   Emacs' tuareg-mode from screwing up code indentation whenever I do
   paragraph-fill.  It doesn't always work though...sigh.

   I will present several implementations of the same function that
   builds up to the final version; some of the implementations work
   while others don't.  Different versions of the same function are
   given identical names but are defined in different local modules,
   so that all versions are accessible without modifying this file.

*)

open Runcode


(***
 *** Introduction and summary of Sorensen et al.
 ***)

(* In a nutshell, Sorensen et al.'s positive supercompiler is partial
   evaluation (PE) using partially static data with conditional
   assumptions.  Specifically:

   (a) upon entering a branch of a dynamic pattern-match, the super-
       compiler adds assumptions to the scrutinee that are valid only
       inside that branch, making the scrutinee partially
       static, and

   (b) it propagates that assumption into the context by replacing all
       references to the scrutinee (in a copy of the context) with the
       partially static datum.

   This file is all about simulating these mechanisms by staging.  The
   intorduction of assumptions in (a) is known as partially static
   data.  The propagation (b) is modeled by updating partially static
   data in place; the delimited nature of the assumptions (a) is
   modeled by installing a dynamic-wind, which undoes the update when
   leaving the conditional branch.

   I'll elaborate on this description using Sorensen et al.'s
   running example, the KMP pattern-matcher.  Here's the reference
   implementation:

   search is a naive, generic implementation.  It takes two strings
   p and s, and decides whether p is a substring of s.

   naive_aab is search naively specialized for the pattern "aab".

   kmp_aab is the manually specialized search for "aab", which
   implements the Knuth-Morris-Pratt (KMP) algorithm.
*)
(*  *)
module Reference = struct
  (* Decide whether p is a substring of s.  Here are some mnemonics for
     variable names:

     p, pp  -- Pattern to search for
     s, ss  -- String to search over
     op     -- Original Pattern, kept for backtracking
     os     -- Original String,  kept for backtracking
  *)
  (* search : char list -> char list -> bool *)
  let rec search p s = loop p s p s
  and loop pp ss op os =
    match pp with
    | [] -> true
    | p::pp' ->
      match ss with
      | [] -> false
      | s::ss' ->
        if s = p then loop pp' ss' op os
        else next op os
  and next op = function
    | [] -> false
    | s::ss -> loop op ss op ss

  (* Naively specialized for p = "aab".  Suffixes indicate what the
     remainder of the pattern looks like at that point.  *)
  let rec naive_aab ss = search_aab ss ss
  and search_aab ss os =
    match ss with
    | [] -> false
    | x::xs ->
      if x = 'a' then search_ab xs os
      else next os
  and search_ab ss os =
    match ss with
    | [] -> false
    | x::xs ->
      if x = 'a' then search_b xs os
      else next os
  and search_b ss os =
    match ss with
    | [] -> false
    | x::xs ->
      if x = 'b' then true
      else next os
  and next = function
    | [] -> false
    | _::xs -> search_aab xs xs (* NB: we can do better than this *)

  (* KMP-style matcher, specialized for p = "aab".  No more `os'.  *)
  let rec kmp_aab = function
    | [] -> false
    | x::xs ->
      if x = 'a' then kmp_ab xs
      else kmp_aab xs
  and kmp_ab = function
    | [] -> false
    | x::xs ->
      if x = 'a' then kmp_b xs
      else kmp_aab xs
  and kmp_b = function
    | [] -> false
    | x::xs ->
      if x = 'b' then true
      else
        (* NB: better than resetting to kmp_aab *)
      if x = 'a'
      then kmp_b xs
      else kmp_ab xs
end

(* A review of the clever shortcuts that KMP takes should make it
   clear where we're heading with this staging exercise. Consider
   the call to the naively specialized function

     naive_aab (str_to_list "aaab")
   i.e.
     naive_aab ('a'::'a'::'a'::'b'::[])

   As far as the matcher is concerned, the contents of the string
   is unknown at the beginning of the call: let's denote that by
   writing

     naive_aab _

   where _ means "some data, don't know what it contains".  Then
   naive_aab calls search_aab and we arrive at the pattern-match

     match _ with
     | [] -> false
     | x::xs -> ...

   The _ is, unbeknownst to the matcher, equal to
   'a'::'a'::'a'::'b'::[], so the second branch is taken.  This
   reveals the head constructor of the previously unknown data, i.e.,

     _ = 'a'::_'

   where _' is a fresh unknown.  Proceeding in this manner, one more
   pattern-match and two equality tests reveal the first two elements
   of the input, and we're at the call

     search_b __ ('a'::'a'::__)

   where __ is another fresh unknown.  Then search_b pattern-matches on
   the first argument, hence getting to

     if x = 'b' then true
     else next os

   where the environment is:

     ss = __
     os = 'a'::'a'::__
     x = 'a'
     xs = 'a'::__

   So we jump to

     next ('a'::'a'::__)

   thence to

     search_aab ('a'::'a'::__) ('a'::'a'::__)

   which re-inspects the first argument and checks again that the first
   two characters are 'a'.  But we can do better than that.  We know the
   first two characters at this point, so we can safely zip right to
   the if-then-else in search_b, jumping directly from the call to
   `next' to

     search_b __ __

   This is exactly what KMP does.  In kmp_b, when the test x = 'b'
   fails, kmp_b resets to kmp_b or kmp_ab, whichever is allowable and
   is the shorter cut.  Note that the KMP matcher doesn't need to keep
   around the parameter `os', because KMP never has to backtrack once the
   pattern to search for is fixed; all branches can be statically resolved
   up to the point where the matcher is forced to inspect an unknown cell.

   The DFA constructed in a textbook formulation of KMP encodes this
   kind of knowledge: if we reach a certain point in the code then we
   partially know the input, therefore we can skip some steps.  In the
   code above, the DFA is embodied in the recursive structure of the
   program.  *)
(*  *)

(* There are two challenges in implementing this optimization.  One is
   that the partially static knowledge about the text (`ss' and `os')
   is a *delimited assumption*, not an unconditional fact.  If we have

     match ls with
     | [] -> (* A *)
     | x::xs -> (* B *)

   then in B we know ls = _::__, but this knowledge is void both in A
   and outside of the match.  In the previous example, we knew that
   search_b always receives ('a'::'a'::_) precisely because reaching
   that function entails taking the cons-branches of some matches and
   the affirmative branches of some "if x=y" statements.  So we need
   to introduce assumptions when we enter a conditional branch and
   make them expire when we leave the branch.

   The other issue is that it's our partially static knowledge about
   `os' that saves us computation, yet we never inspect `os' to get
   that knowledge.  In any call to search_b, we know os =
   'a'::'a'::_ because of pattern-matches on `ss', not on `os'!  So
   somehow the information learned about `ss' has to trickle to `os'.
   This is the crucial difference between supercompilation and PE.

   Sorensen et al.'s positive supercompiler gives a unique name to
   each data so that all copies of the same data have the same name.
   When the supercompiler enters a conditional branch within which
   `ss' = 'a'::_ holds, then it propagates this information to all
   copies by replacing all occurrences of (the unique name given to)
   `ss' in the context and in all subterms.

   The main idea of this article is to capture this information
   sharing by physically sharing partially static data, and updating
   it in-place.  In KMP, `ss' and `os' will share the same memory
   location.  Pattern-matches on `ss' will modify `ss', and therefore
   `os' as well, to reflect the assumptions introduced by the match.
   We install a handler that will ensure that this update is undone
   upon leaving the branch.

*)
(*  *)

(***
 *** Staging the matcher without supercompilation.
 ***)

(* So let's try to stage the naive matcher; I'll gradually work up to
   a complete solution.  First, a naive specialization on the pattern
   doesn't work at all.  Because the termination measure of the
   unstaged matcher includes the text and not just the pattern, we end
   up with a nonterminating generator.  It keeps generating dynamic
   matches that deconstruct `ss' further and further ad infinitum.

   This corresponds to driving without a check to see if a state has
   been seen before, which produces an infinite tree in most cases.
*)

(* A non-terminating matcher specializer/generator.  *)
module Nonterm = struct
  let rec search_gen p = .<fun s -> .~(loop_gen p .<s>. p .<s>.)>.
  and loop_gen pp ss op os =
    match pp with
    | [] -> .<true>.
    | p::pp ->
      .<match .~ss with
      | [] -> false
      | s::ss when p = s -> .~(loop_gen pp .<ss>. op os)
      | s::ss -> .~(next_gen op os)>.
  and next_gen op os =
    .<match .~os with
    | [] -> false
    | s::ss ->
      (* Reset the pattern and advance the text.  *)
      .~(loop_gen op .<ss>. op .<ss>.)
      >.
end

(* So we can't just keep unrolling indefinitely.  The standard, and
   quite obvious, solution is to generate not flat-line code but a
   recursive function, and to call back to that function when we reset
   the pattern and advance the text (see the commented line in the
   non-terminating generator).

   We do this by inserting "let rec" in the generated code and
   memoizing the name of the generated function.  When we find that
   we're processing a pattern that has been seen before, we simply
   call the function whose name was memoized.  In PE-speak, we
   introduce specialization points to avoid specializing the same
   expression twice.  The implementation technique is basically that
   of Swadi et al. [2], except that we're dealing with infinite code
   duplication.

   From the supercompilation point of view, this memoization
   corresponds to a restricted form of ancestor checking and folding,
   where the supercompiler tests if a leaf node is similar to a
   previously driven node before deciding to drive that leaf node
   further.

*)

(* Memoization table + state-continuation monad.  The continuation
   part is not needed, for now.  *)
module MemoTable : sig
  type ('k,'v) table
  val lookup : ?eq:('k -> 'k -> bool) -> 'k -> ('k,'v) table -> 'v option
  val add : 'k -> 'v -> ('k,'v) table -> ('k,'v) table
  val empty : ('k,'v) table
  val size : ('k,'v) table -> int

  type ('a,'s,'k) monad
  val return : 'a -> ('a,'s,'k) monad
  val bind : ('a,'s,'k) monad -> ('a -> ('b,'s,'k) monad) -> ('b,'s,'k) monad
  val get : ('s,'s,'k) monad
  val set : 's -> (unit,'s,'k) monad
  val modify : ('s -> 's) -> (unit,'s,'k) monad
  val run_monad : ('a,'s,'a) monad -> 's -> 'a
end = struct
  type ('k, 'v) table = ('k * 'v) list
  let lookup ?(eq = (=)) x alist =
    let rec assoc = function
      | [] -> None
      | (y,v)::rest -> if eq x y then Some v else assoc rest
    in assoc alist
  and add x y alist = (x,y)::alist
  and empty = []
  and size t = List.length t

  type ('a,'s,'k) monad = 's -> ('s -> 'a -> 'k) -> 'k
  let return x = fun s k -> k s x
  let bind m f = fun s k -> m s (fun s' x -> f x s' k)
  let get = fun s k -> k s s
  let set s = fun _ k -> k s ()
  let modify f = fun s k -> k (f s) ()

  let run_monad m init_state = m init_state (fun _ x -> x)
end

(* The following module implements let rec insertion.  Ideally, we
   would like to generate a flat binding, like

    let rec f1 = abc
    and f2 = def
    and f3 = ghi
    in jkl

   But this cannot be achieved currently unless the number of bindings
   is statically fixed.  We replace this with nested let rec,

    let rec f1 =
      let rec f2 =
        let rec f3 = ghi
        in def
      in abc
    in jkl

   This has some disadvantages:

    - The body of f1 (jkl in this code) cannot refer to f3, so there is some
      limitation to avoiding code duplication with this method.  This
      corresponds to a limitation in the monadic memoization technique:
      memoization cannot float code generated inside an escape out of that
      escape.  The second

    - Nested let recs are aesthetically displeasing, and makes it harder to
      read the generated code when the programmer wants to check if it's as
      intended.

   as well as an advantage:

    - The generator is pure, so scope extrusion is impossible.

   A near-future version of MetaOCaml is expected to include
   combinators that produce the flattened bindings.

*)
module Memoization = struct
  let return = MemoTable.return
  let bind = MemoTable.bind
  let get = MemoTable.get
  let set = MemoTable.set
  let modify = MemoTable.modify

  let memoize ?(eq=(=)) key fcn call =
    bind get (fun table ->
        match MemoTable.lookup ~eq key table with
        | Some f -> call f
        | None ->
          (* No inversion of the order of bindings like Swadi et
             al. because we don't have a binding time problem.  *)
          bind get (fun table ->
              return
              .<let rec f = .~(MemoTable.run_monad fcn
                                 (MemoTable.add key .<f>. table))
              in .~(MemoTable.run_monad (call .<f>.) table)>.
            ))

  let run_monad m = MemoTable.run_monad m MemoTable.empty

  let save f = bind get (fun s -> return (f s))
  let resume s m = MemoTable.run_monad m s
end

(* A naively memoized version that produces correct but inefficient
   code -- basically the same code as Reference.naive_aab.  The reason
   is that we don't propagate assumptions about `ss' to `os'.

   As we will see later, the memoization scheme used here is
   suboptimal.  Keying the memo table with pp only is sufficient to
   ensure termination but insufficient to generate quality code.  *)
module NaiveMemo = struct
  open Memoization
  let rec search_gen (p : char list) =
    .<fun s -> .~(run_monad @@ loop_gen p .<s>. p .<s>.)>.
  and loop_gen pp ss op os =
    match pp with
    | [] -> return .<true>.
    | p::pp' ->
      memoize pp
        (save (fun state ->
             .<fun ss os ->
               match ss with
               | [] -> false
               | s::ss ->
                 if p = s
                 then .~(resume state @@ loop_gen pp' .<ss>. op .<os>.)
                 else .~(resume state @@ next_gen op .<os>.)>.
           ))
        (fun f -> return .<.~f .~ss .~os>.)
  and next_gen op os =
    save (fun state ->
        .<match .~os with
        | [] -> false
        | s::ss ->
          (* Reset the pattern and advance the text.  *)
          .~(resume state @@ loop_gen op .<ss>. op .<ss>.)
          >.
      )
  and search p = !. (search_gen p)
end


(***
 *** Staging with delimited assumptions.
 ***)

(*

   Quick recap.  The partial knowledge about os is:

   - determined by pattern matching on ss, without touching os

   - different for each branch of the "match ss' with" in loop_gen.

   So we need to:

   - have partially static data

   - share static assumptions between copies of the same data

   - delimit the lifetime of the assumption

 *)

(* Partially static data types with knowledge shared through
   mutation.  *)
module PSData = struct
  (* sd is a wrapper providing static information about dynamic data.  An sd
     value should be of the form
     { dynamic = .<x>.; static = (* None or Some const *) }

     's is the static representation of the payload
     'd is the dynamic payload

     's and 'd may not match in recursive datatypes, like lists: 's =
     int ps_list whereas 'd = int list.  The static representation is
     not just int list partial because every cons must be marked
     with metadata -- partial staticness is a mixin, not a simple wrapper.

     We need to know both 's and 'd to be able to type the `forget' function,
     which discards static information.  *)
  type ('s,'d) sd = { mutable dynamic : 'd code;
                      mutable static : 's option; }

  let forget { dynamic = x } = x

  (* Grab a dynamic or static value and package it in sd.  *)
  let unknown : 'd code -> ('s,'d) sd = fun x -> { dynamic = x;
                                                   static = None; }
  and known : 's -> 'd code -> ('s,'d) sd = fun s d -> { dynamic = d;
                                                         static = Some s }

  (* In a partially static list, we need to mix in sd throughout the whole
     structure.

     Type-level open recursion would be the best general mechanism to
     use here, but in OCaml it makes type errors completely
     unreadable, so I've hard-coded the mixin.  *)
  type ('s,'d) ps_list_cell = Nil
                            | Cons of ('s,'d) sd * ('s,'d) ps_list
  and ('s,'d) ps_list = (('s,'d) ps_list_cell, 'd list) sd

  (* Check if a partial datum is Known or Unknown.  *)
  let is_known x = x.static <> None
  let is_unknown x = not @@ is_known x

  (* NB: cons breaks the invariant that the `dynamic' field contains just a
     dynamic variable, so it can lead to code size explosion.  Use with
     care.  *)
  let nil () = { dynamic = .<[]>.; static = Some Nil }
  and cons x xs = { dynamic = .<.~(x.dynamic)::.~(xs.dynamic)>.;
                              static = Some (Cons (x, xs)) }

  (* Introduce a (temporally) delimited assumption x = v, valid only
     while executing the thunk.  *)
  let assuming_eq x v thunk =
    let saved = x.static in
    try x.static <- Some v;
      let ret = thunk () in
      x.static <- saved;
      ret
    with e -> x.static <- saved; raise e

  (* Like assuming_eq, but change the dynamic representation.  *)
  let alias x y thunk =
    let saved = x.dynamic in
    try x.dynamic <- y;
      let ret = thunk () in
      x.dynamic <- saved;
      ret
    with e -> x.dynamic <- saved; raise e

  (* Pattern-match on a list using static information if it's
     available.  Otherwise, generate a dynamic match and generate its
     branches under delimited assumptions.  *)
  let match_ls ls nil_clause cons_clause =
    match ls.static with
    | Some Nil -> nil_clause ()
    | Some (Cons (x,xs)) -> cons_clause x xs
    | None ->
      .<match .~(forget ls) with
      | [] -> .~(assuming_eq ls Nil nil_clause)
      | x::xs -> .~(let x = unknown .<x>.
                    and xs = unknown .<xs>.
                    in assuming_eq ls (Cons (x,xs))
                      (fun () -> cons_clause x xs))>.

                 let ifeq x c then_clause else_clause =
                   let sc =
                     match c.static with
                     | None -> invalid_arg "ifeq: missing static info"
                     | Some sc -> sc
                   in
                   match x.static with
                   | Some v when v = sc -> then_clause ()
                   | Some _ -> else_clause ()
                   | None ->
                     .<if .~(forget x) = .~(forget c)
                     then .~(assuming_eq x sc then_clause)
                     else .~(else_clause ())>.

                          (* Generate a .<fun x -> ...>.; wrap the formal parameter .<x>. in sd before
                             passing it to the callback that generates the function body.  *)
                          let dfun body = .<fun x -> .~(body (unknown .<x>.))>.

                                                     (* Check if xs is a renaming of ys assuming that every dynamic field
                                                        is of the form .<x>. where x is a variable.  IOW, xs and ys
                                                        should be isomorphic as trees, except sharing of nodes tagged
                                                        Unknown must be the same.  For example, given the bindings

                                                          (* keep in mind unknown x = ref unknown x *)
                                                          let w = unknown .<w>.
                                                          and x = unknown .<x>.
                                                          and y = unknown .<y>.
                                                          and z = unknown .<z>.

                                                        where the future-stage w,x,y,z are bound somewhere else, we have

                                                          is_renaming (nil ()) (cons y z) = false
                                                          is_renaming (nil ()) z          = false
                                                          is_renaming (cons w x) (cons y z) = true
                                                          is_renaming (cons w x) (cons w z) = true
                                                          is_renaming (cons w (cons w z))
                                                                      (cons y (cons y z))   = true

                                                        but

                                                          is_renaming (cons w (cons y z))
                                                                      (cons y (cons y z)) = false

                                                        because the sharing is different in the last example.

                                                        For simplicity, this version of is_renaming handles only
                                                        (partially static) lists of ground types, like (char, char)
                                                        ps_list.

                                                     *)
                                                     let is_renaming xs ys =
                                                       (* This is a naive implementation.  We talk down xs and ys while
                                                          checking that they have the same constructors.  xvars maintains
                                                          the list of variables that were encountered while walking
                                                          through xs, and yvars does the same for ys.  When we reach
                                                          variables x (in xs) and y (in ys), we check that x is
                                                          physically equal to the i-th element of xvars iff y is
                                                          physically equal to the i-th element of yvars.
                                                       *)
                                                       let rec cmp_sharing xvars x yvars y =
                                                         match xvars, yvars with
                                                         | [], [] -> true
                                                         | xv::xvars, yv::yvars -> (x == xv) = (y == yv) &&
                                                                                   cmp_sharing xvars x yvars y
                                                         | _, _ -> false
                                                       and cmp_lists xvars xs yvars ys =
                                                         match xs.static, ys.static with
                                                         | Some Nil, Some Nil -> true
                                                         | Some (Cons (x,xs)), Some (Cons (y,ys)) ->
                                                           cmp_conses xvars x xs yvars y ys
                                                         | None, None ->
                                                           (* Simplifying assumption: the input lists carry ground types,
                                                              so the tail is the only place where vars of the right type
                                                              can occur.  Hence those variables always match.  *)
                                                           true
                                                         | _, _ -> false
                                                       and cmp_conses xvars x xs yvars y ys =
                                                         match x.static, y.static with
                                                         | Some x, Some y -> x = y
                                                         | None, None ->
                                                           cmp_sharing xvars x yvars y &&
                                                           cmp_lists (x::xvars) xs (y::yvars) ys
                                                         | _, _ -> false
                                                       in cmp_lists [] xs [] ys

  (* Copy a list so that it doesn't affected by subsequent
     introduction of assumptions.  Sharing is preserved, so the result
     of is_renaming doesn't change.  *)
  let rec freeze_list freeze_elem xs =
    let open MemoTable in
    bind get (fun (elems, lists) ->
        match lookup ~eq:(==) xs lists with
        | Some x -> return x
        | None ->
          bind
            (match xs.static with
             | Some Nil -> return @@ nil ()
             | Some (Cons (x,xs)) ->
               bind (freeze_elem x) (fun y ->
                   bind (freeze_list freeze_elem xs) (fun ys ->
                       return @@ cons y ys))
             | None -> return @@ { static = xs.static; dynamic = xs.dynamic })
            (fun ys ->
               bind (set (elems, add xs ys lists)) (fun () ->
                   return ys))
      )
  (* Freeze a ground type.  *)
  let freeze_ground x =
    let open MemoTable in
    bind get (fun (elems, lists) ->
        match lookup ~eq:(==) x elems with
        | Some y -> return y
        | None ->
          let y = { static = x.static; dynamic = x.dynamic } in
          bind (set (add x y elems, lists)) (fun () ->
              return y))
end

(* Using delimited assumptions without memoization of course gives a divergent
   generator.  However, it does illustrate how to use the combinators.  This
   module contains that code example as well as a simpler, terminating example
   for illustration.  *)
module DelimAssmNonterm = struct
  open PSData
  let rec search_gen p =
    .<fun s -> .~(let s = unknown .<s>. in
                  loop_gen p s p s)>.
  and loop_gen pp ss op os =
    match pp with
    | [] -> .<true>.
    | p::pp ->
      match_ls ss
        (fun () -> .<false>.)
        (fun s ss ->
           ifeq s (known p .<p>.)
             (fun () -> loop_gen pp ss op os)
             (fun () -> next_gen op os))
  and next_gen op os =
    match_ls os
      (fun () -> .<false>.)
      (fun s ss -> loop_gen op ss op ss)
  and search p = !. (search_gen p)

  (* Here's an example where there is no termination issue.  Note how
     the nonlinear use of zs is tracked.  *)
  let rec contrived zs =                (* unstaged version *)
    let f xs ys =
      match xs with
      | [] -> length xs + length ys
      | x::xs -> 0
    in f zs (1::zs)
  and length = function [] -> 0 | _::xs -> 1 + length xs

  let rec gen_len xs =
    match_ls xs
      (fun () -> .<0>.)
      (fun _ xs -> .<1 + .~(gen_len xs)>.)
  let gen_contrived = .<fun zs ->   (* generator *)
    .~(
      let zs = unknown .<zs>. in
      let f xs ys =
        match_ls xs
          (fun () -> .<.~(gen_len xs) + .~(gen_len ys)>.)
          (fun _ _ -> .<0>.)
      in f zs (cons (known 1 .<1>.) zs)
    )>.
end

(* Overwrite combinators in PSData with versions that work in the
   Memoization.monad.  This is especially important with assuming_eq,
   because the non-monadic version defined in PSData is error-prone
   under a monad: if thunk returns a monad, which is a function,
   assuming_eq x v thunk installs / undoes the assumption when thunk
   runs / returns, not when the monadic action runs / returns!  *)
module PSDataMemo = struct
  include PSData
  open Memoization

  let assuming_eq x v thunk =
    save (fun state ->
        let saved = x.static in
        x.static <- Some v;
        try resume state @@
          bind (thunk ())
            (fun ret -> x.static <- saved; return ret)
        with e -> x.static <- saved; raise e)

  let alias x y thunk =
    save (fun state ->
        let saved = x.dynamic in
        x.dynamic <- y;
        try resume state @@
          bind (thunk ())
            (fun ret -> x.dynamic <- saved; return ret)
        with e -> x.dynamic <- saved; raise e)

  let match_ls ls nil_clause cons_clause =
    match ls.static with
    | Some Nil -> nil_clause ()
    | Some (Cons (x,xs)) -> cons_clause x xs
    | None ->
      (* Note: the resume state must not be moved before assuming_eq,
         because then the thunk passed to assuming_eq would just
         return the monad action without executing it.  *)
      save (fun state ->
          .<match .~(forget ls) with
          | [] -> .~(resume state @@ assuming_eq ls Nil nil_clause)
          | x::xs -> .~(resume state @@
                        let x = unknown .<x>.
                        and xs' = unknown .<xs>.
                        in
                        assuming_eq ls (Cons (x, xs'))
                          (fun () -> cons_clause x xs'))
                     >.)

  (* Generate conditionals of the form .<if x = c then ... else
     ...>. with delimited assumptions.  *)
  let ifeq x c then_clause else_clause =
    let sc =
      match c.static with
      | None -> invalid_arg "ifeq: missing static info"
      | Some sc -> sc
    in
    match x.static with
    | Some v when v = sc -> then_clause ()
    | Some _ -> else_clause ()
    | None ->
      save (fun state ->
          .<if .~(forget x) = .~(forget c)
          then .~(resume state @@ assuming_eq x sc then_clause)
          else .~(resume state @@ else_clause ())>.)

  (* Monomorphic version that ensures the CPS'ed constant is
     pretty-printed properly.  *)
  let ifeq_char x (c:char) then_clause else_clause =
    match x.static with
    | Some v when v = c -> then_clause ()
    | Some _ -> else_clause ()
    | None ->
      save (fun state ->
          .<if .~(forget x) = c
          then .~(resume state @@ assuming_eq x c then_clause)
          else .~(resume state @@ else_clause ())>.)

  let dfun body =
    save (fun state ->
        .<fun x -> .~(resume state @@ body (unknown .<x>.))>.)
end

(* Now we're ready to tackle supercompilation.  Basically, we just
   replace all occurrence of match with match_ls and "if x = c" with
   ifeq_char.  The tricky part is memoization.  We must include all
   the state variables pp,ss,op,os in the memo key because if they
   carry different values, then they require different processing.
   However, we don't want to insist that the quadruple pp,ss,op,os be
   equal in the sense of (=) to be able to reuse a generated recursive
   function, because in all likelihood the dynamic values will differ.

   For example, if f_1 was generated when

     (pp,ss,op,os) = ("ab",ss,"aab",'a'::ss)

   where ss has statically unknown value, then we'd still like to
   reuse f_1 for the case when

     (pp,ss,op,os) = ("ab",ts,"aab",'a'::ts)

   where ts is some other variable with statically unknown value.
   Therefore, the comparison must ignore differences in variable
   names.  But at the same time, we don't want to reuse f_1 if the
   state is

     (pp,ss,op,os) = ("ab",ts,"aab",'a'::us)

   where ss and os do not share the same variable.  (This situation is
   never encountered with the string search example, but it's
   unavoidable in general.)  Hence we should compare the sharing of
   dynamic nodes, but not the nodes themselves -- in other words, the
   keys should be compared by graph isomorphism.

   This generator returns the same code as Sorensen et al., except
   that let recs are nested.  The positive supercompiler (and hence
   the generator here) generates redundant conditionals, which look
   like

     if x = 'a' then foo
     else if x = 'a' then bar
     else baz

   This happens because we track positive information, x = 'a', but
   not negative information, x <> 'a'.  We could easily extend this
   approach by carrying more precise characterizations of the data in
   the partially static data type, like a set of possible values.

*)
(*  *)

module DelimAssmMemo = struct
  open PSData
  open Memoization
  open PSDataMemo

  let dag (pp,ss,op,os) =
    let conv =
      bind (freeze_list freeze_ground ss) (fun ss' ->
          bind (freeze_list freeze_ground os) (fun os' ->
              return (pp,ss',op,os')))
    in
    MemoTable.run_monad conv (MemoTable.empty, MemoTable.empty)

  let alpha_ident_kmp (pp,ss,op,os) (pp',ss',op',os') =
    pp = pp' && op = op' && is_renaming ss ss' && is_renaming os os'

  let rec search_gen (p : char list) =
    .<fun s -> .~(let s' = unknown .<s>.
                  in run_monad @@ loop_gen p s' p s')>.
  and loop_gen pp ss op os =
    match pp with
    | [] -> return .<true>.
    | p::pp' ->
      let gen_body ss =
        match_ls ss
          (fun () -> return .<false>.)
          (fun s ss ->
             ifeq_char s p
               (fun () -> loop_gen pp' ss op os)
               (fun () -> next_gen op os))
      in
      (* This is_known check is optional; it suppresses trivial let
         recs of the form

           let rec f x = (some constant)
           in ...

         that are aesthetically better inlined. *)
      (*if is_known ss
        then gen_body ss
        else *)
      memoize ~eq:alpha_ident_kmp (dag (pp,ss,op,os))
        (dfun (fun ss' -> alias ss (forget ss') (fun () -> gen_body ss)))
        (fun f -> return .<.~f .~(forget ss)>.)
  and next_gen op os =
    match_ls os
      (fun () -> return .<false>.)
      (fun s ss -> loop_gen op ss op ss)
  and search p = !. (search_gen p)



  (* This is the contrived example mentioned earlier, but with a
     cons-branch that wouldn't terminate without proper
     memoization.  *)
  let rec contrived zs =                (* unstaged version *)
    let f xs ys =
      match xs with
      | [] -> length xs + length ys
      | x::xs -> length xs
    in f zs (1::zs)
  and length = function [] -> 0 | _::xs -> 1 + length xs

  let freeze ws =
    MemoTable.run_monad (freeze_list freeze_ground ws)
      (MemoTable.empty, MemoTable.empty) (*
    let conv =
      bind (freeze_list freeze_ground ss) (fun ss' ->
      bind (freeze_list freeze_ground os) (fun os' ->
      return (pp,ss',op,os')))
    in
    MemoTable.run_monad conv (MemoTable.empty, MemoTable.empty) *)

  let alpha_ident xs ys = is_renaming xs ys

  let (+!) x y =
    bind get (fun table ->
        return .<.~(resume table x) + .~(resume table y)>.)

  let rec gen_len ws =
    let gen_body ws =
      match_ls ws
        (fun () -> return .<0>.)
        (fun _ ws -> return .<1>. +! gen_len ws)
    in
    if is_known ws
    then gen_body ws
    else
      memoize ~eq:alpha_ident (freeze ws)
        (dfun (fun ws' -> alias ws (forget ws') (fun () ->
             gen_body ws)))
        (fun f -> return .<.~f .~(forget ws)>.)
  and gen_contrived () = dfun (fun zs ->
      let f xs ys =
        match_ls xs
          (fun () -> gen_len xs +! gen_len ys)
          (fun _ ws -> gen_len xs +! gen_len xs)
      in f zs (cons (known 1 .<1>.) zs))
  let generated_contrived = run_monad @@ gen_contrived ()
end


(* What happens if we key the memo table with only completely static
   data?  For the KMP example, it still works because when ss is
   completely dynamic (i.e. it tests false for is_known), then the
   length of pp determines the length of the static portion of os.  We
   opted for a more generalizable approach above, for illustrative
   purposes.  *)
module DelimAssmMemoOnlyStatic = struct
  open PSData
  open Memoization
  open PSDataMemo

  let rec search_gen (p : char list) =
    .<fun s -> .~(let s' = unknown .<s>.
                  in run_monad @@ loop_gen p s' p s')>.
  and loop_gen pp ss op os =
    match pp with
    | [] -> return .<true>.
    | p::pp' ->
      let gen_body ss =
        match_ls ss
          (fun () -> return .<false>.)
          (fun s ss ->
             ifeq_char s p
               (fun () -> loop_gen pp' ss op os)
               (fun () -> next_gen op os))
      in
      if is_known ss
      then gen_body ss
      else
        memoize (pp,op)
          (dfun (fun ss' -> alias ss (forget ss') (fun () -> gen_body ss)))
          (fun f -> return .<.~f .~(forget ss)>.)
  and next_gen op os =
    match_ls os
      (fun () -> return .<false>.)
      (fun s ss -> loop_gen op ss op ss)
  and search p = !. (search_gen p)
end



(***
 *** Test code.
 ***)

let enum start stop =
  let rec go acc n =
    if n < start then acc
    else go (n::acc) (n-1)
  in go [] stop
let str_to_list s =
  List.map (String.get s) (enum 0 (String.length s - 1))

let test_cases =
  [("a","",false);
   ("a","abc",true);
   ("a","ba",true);
   ("a","aaa",true);
   ("a","aa",true);
   ("a","bbb",false);

   ("aa","",false);
   ("aa","abc",false);
   ("aa","ba",false);
   ("aa","aaa",true);
   ("aa","aa",true);
   ("aa","bbb",false);
   ("aa","bba",false);

   ("aab","",false);
   ("aab","abc",false);
   ("aab","ba",false);
   ("aab","aaa",false);
   ("aab","aaab",true);
   ("aab","aaba",true);
   ("aab","caba",false);
   ("aab","aa",false);
   ("aab","bbb",false);
   ("aab","bba",false);

   ("aaab","",false);
   ("aaab","abc",false);
   ("aaab","ba",false);
   ("aaab","aaa",false);
   ("aaab","aaab",true);
   ("aaab","aaaba",true);
   ("aaab","aaaab",true);
   ("aaab","aaba",false);
   ("aaab","caba",false);
   ("aaab","aa",false);
   ("aaab","bbb",false);
   ("aaab","bba",false);

   (* For testing the test code.  *)
      (*
      ("this should fail","bba",true);
      ("this should fail","this should fail",false);
      *)
  ]


(* Test a matcher.  Test is successful if nothing is printed.  *)
let test f =
  List.iter (fun (pat,text,expect) ->
      if f (str_to_list pat) (str_to_list text) <> expect
      then Printf.printf "FAILED: \"%s\" \"%s\"\n" pat text)
    test_cases

(* Test a matcher that is specialized to a fixed pattern.  The pattern
   must appear in the test_cases above.  *)
let test_spec f pat =
  List.iter (fun (pat',text,expect) ->
      if pat = pat' && f (str_to_list text) <> expect
      then Printf.printf "FAILED: \"%s\" \"%s\"\n" pat text)
    test_cases


(*

As a special exception to the Q Public Licence, you may develop
application programs, reusable components and other software items
that link with the original or modified versions of the Compiler
and are not made available to the general public, without any of the
additional requirements listed in clause 6c of the Q Public licence.

----------------------------------------------------------------------

                   THE Q PUBLIC LICENSE version 1.0

              Copyright (C) 1999 Troll Tech AS, Norway.
                  Everyone is permitted to copy and
                  distribute this license document.

The intent of this license is to establish freedom to share and change
the software regulated by this license under the open source model.

This license applies to any software containing a notice placed by the
copyright holder saying that it may be distributed under the terms of
the Q Public License version 1.0. Such software is herein referred to
as the Software. This license covers modification and distribution of
the Software, use of third-party application programs based on the
Software, and development of free software which uses the Software.

                            Granted Rights

1. You are granted the non-exclusive rights set forth in this license
provided you agree to and comply with any and all conditions in this
license. Whole or partial distribution of the Software, or software
items that link with the Software, in any form signifies acceptance of
this license.

2. You may copy and distribute the Software in unmodified form
provided that the entire package, including - but not restricted to -
copyright, trademark notices and disclaimers, as released by the
initial developer of the Software, is distributed.

3. You may make modifications to the Software and distribute your
modifications, in a form that is separate from the Software, such as
patches. The following restrictions apply to modifications:

      a. Modifications must not alter or remove any copyright notices
      in the Software.

      b. When modifications to the Software are released under this
      license, a non-exclusive royalty-free right is granted to the
      initial developer of the Software to distribute your
      modification in future versions of the Software provided such
      versions remain available under these terms in addition to any
      other license(s) of the initial developer.

4. You may distribute machine-executable forms of the Software or
machine-executable forms of modified versions of the Software,
provided that you meet these restrictions:

      a. You must include this license document in the distribution.

      b. You must ensure that all recipients of the machine-executable
      forms are also able to receive the complete machine-readable
      source code to the distributed Software, including all
      modifications, without any charge beyond the costs of data
      transfer, and place prominent notices in the distribution
      explaining this.

      c. You must ensure that all modifications included in the
      machine-executable forms are available under the terms of this
      license.

5. You may use the original or modified versions of the Software to
compile, link and run application programs legally developed by you or
by others.

6. You may develop application programs, reusable components and other
software items that link with the original or modified versions of the
Software. These items, when distributed, are subject to the following
requirements:

      a. You must ensure that all recipients of machine-executable
      forms of these items are also able to receive and use the
      complete machine-readable source code to the items without any
      charge beyond the costs of data transfer.

      b. You must explicitly license all recipients of your items to
      use and re-distribute original and modified versions of the
      items in both machine-executable and source code forms. The
      recipients must be able to do so without any charges whatsoever,
      and they must be able to re-distribute to anyone they choose.

      c. If the items are not available to the general public, and the
      initial developer of the Software requests a copy of the items,
      then you must supply one.

                       Limitations of Liability

In no event shall the initial developers or copyright holders be
liable for any damages whatsoever, including - but not restricted to -
lost revenue or profits or other direct, indirect, special, incidental
or consequential damages, even if they have been advised of the
possibility of such damages, except to the extent invariable law, if
any, provides otherwise.

                             No Warranty

The Software and this license document are provided AS IS with NO
WARRANTY OF ANY KIND, INCLUDING THE WARRANTY OF DESIGN,
MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.

                            Choice of Law

This license is governed by the Laws of France.
 *)

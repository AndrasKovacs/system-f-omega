# system-f-omega

What we have here is an intrinsically typed formalization of impredicative System F-omega, plus its normalization by hereditary substitution.

The presentation follows [Altenkirch and Keller](http://www.cs.nott.ac.uk/~psztxa/publ/msfp10.pdf), but we need significant extra machinery to adapt it to F-omega. 

We need normalization and a large part of its correctness proof for types (which is essentially a simply typed lambda calculus) in order to be able to define the term operations in an intrinsically well-typed way. This consitutes the bulk of the line count of this project; I could've probably copied Altenkirch and Keller and written some proofs to glue it to System F-omega, but I considered it a valuable effort to redo it in a way that by default mirrors System F-omega term operations. 

Most notably, what we **don't have** is a termination proof for term substitution. It eventually dawned on me that the main reason why hereditary substitution works for STLC is because applying a term to a spine is structurally recursive in the *type* of the term, and this is irreparably foiled in impredicative System F. Here, if a term has type `∀ (a : k) . t`, if we apply it to `t' : k` the resultant type would be a `t [a := t']` substitution, which isn't smaller than the starting type by any measure. For example, we can have `id = Λ (a : ⋆). λ (x : a) . x` with `id : ∀ (a : *). a → a`, and then `id [∀ (a : *). a → a] id` has the same type (definitionally) as `id`. 

This setup would be amenable to simple termination proofs only for predicative or stratified System F, similarly to what's in the paper of [Eades and Stump](http://homepage.cs.uiowa.edu/~astump/papers/pstt-2010.pdf). 

However, eta expansion, renaming and type substition is still total (as certified by Agda) and hopefully useful. We also have a rather large chunk of the correctness proof for STLC's normalization, and we can play around with the F-omega normalization function.


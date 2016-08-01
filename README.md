# system-f-omega
System F-omega normalization by hereditary substitution in Agda

What we have here is a formalization of impredicative System F-omega, plus normalization by hereditary substitution.

The presentation follows [Altenkirch and Keller](http://www.cs.nott.ac.uk/~psztxa/publ/msfp10.pdf), but we need significant extra machinery to adapt it to F-omega. 

We need normalization and a large part of its correctness proof for types (which is essentially simply typed lambda calculus) in order to be able to define the term operations. 

Most notably, what we **don't have** is a termination proof for term substitution. It eventually dawned on me that the main reason why hereditary subst works for STLC is because applying a term to a spine is structurally recursive in the *type* of the term, and this is irreparably foiled in impredicative System F. Here, if a term has type `∀ (a : k) . t`, if we apply it to `t' : k` the resultant type would be a `t [a := t']` substitution, which isn't smaller than the starting type by any measure. For example, we can have `id = Λ (a : ⋆). λ (x : a) . x` with `id : ∀ (a : *). a → a`, and then `id [∀ (a : *). a → a] id` has the same type (definitionally) as `id`. 

This setup would be amenable to termination proofs only for predicative or stratified System F, similarly to what's in the paper of [Eades and Stump](http://homepage.cs.uiowa.edu/~astump/papers/pstt-2010.pdf). 

However, eta expansion, renaming and type substition is still total (as certified by Agda) and hopefully useful. We also have a rather large chunk of the correctness proof for STLC's normalization, and we can play around with the F-omega normalization function.


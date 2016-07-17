This is a copy of the Agda hereditary-substitution-based STLC beta-eta
normalizer by Keller and Altenkirch [1], modified to no longer perform
eta expansion.  I.e., whereas the original normalizer produced
beta-short eta-long terms, this one only performs beta-reductions,
producing beta-normal results.  Obviously, this means it no longer
decides beta-eta-equivalence: those theorems have been commented out,
but the correctness of normalization theorem (called 'completeness')
has been updated.

The necessary changes were trivial; the point was to better understand
what role eta-longness played in the termination argument for
hereditary substitution. Answer: none!  The key here is the spine
representation of iterated application, which reifies in structural
recursion on types the meta-argument for the termination of hereditary
substitution found in some paper proofs.  E.g., the Lemma 2.2 in
Harper and Licata's /Mechanizing Metatheory in a Logical Framework/,
which says:

  If

    hereditary substitution of a normal (n:T) for x in a neutral e = a normal (n':T')

  then type T' is structural sub term of T.

[1] I copied the source code from:
http://www.lix.polytechnique.fr/~keller/Recherche/hsubst.html; Keller
and Altenkirch's paper explaining the code, /Hereditary Substitutions
for Simple Types, Formalized/, is available here:
http://hal.inria.fr/docs/00/52/06/06/PDF/msfp10.pdf

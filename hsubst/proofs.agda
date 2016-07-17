--------------------------------------------------------------------------------
-- The module implements:                                                     --
--   - a predicate that defines the βη-equivalence on terms                   --
--   - the most important theorems about hereditary substitutions we prove:   --
--     completeness, soundness and stability. Completeness and soundness      --
--     that the βη-equivalence is decidable, and the normalizer defined with  --
--     the aid of hereditary substitutions decides the βη-equivalence.        --
--------------------------------------------------------------------------------

    -- This program is free software: you can redistribute it and/or modify
    -- it under the terms of the GNU General Public License as published by
    -- the Free Software Foundation, either version 3 of the License, or
    -- (at your option) any later version.

    -- This program is distributed in the hope that it will be useful,
    -- but WITHOUT ANY WARRANTY; without even the implied warranty of
    -- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    -- GNU General Public License for more details.

    -- You should have received a copy of the GNU General Public License
    -- along with this program.  If not, see <http://www.gnu.org/licenses/>.

    -- Copyright Thorsten Altenkirch and Chantal Keller, 2010

module proofs where


infix 10 _βη-≡_


open import hsubst
open import lemmas1
open import lemmas2
open import lemmas3
open import lemmas4

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


-- βη-equality

data _βη-≡_ {Γ : Con} : {σ : Ty} → Tm Γ σ → Tm Γ σ → Set where
  brefl : ∀ {σ} → {t : Tm Γ σ} → t βη-≡ t
  bsym : ∀ {σ} → {t₁ t₂ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₁
  btrans : ∀ {σ} → {t₁ t₂ t₃ : Tm Γ σ} → t₁ βη-≡ t₂ → t₂ βη-≡ t₃ → t₁ βη-≡ t₃
  congΛ : ∀ {σ τ} → {t₁ t₂ : Tm (Γ , σ) τ} → (t₁ βη-≡ t₂) → Λ t₁ βη-≡ Λ t₂
  congApp : ∀ {σ τ} → {t₁ t₂ : Tm Γ (σ ⇒ τ)} → {u₁ u₂ : Tm Γ σ} → t₁ βη-≡ t₂ → u₁ βη-≡ u₂ → app t₁ u₁ βη-≡ app t₂ u₂
  beta : ∀ {σ τ} → {t : Tm (Γ , σ) τ} → {u : Tm Γ σ} → app (Λ t) u βη-≡ hsubst.subst t vz u
  eta : ∀ {σ τ} → {t : Tm Γ (σ ⇒ τ)} → Λ (app (wkTm vz t) (var vz)) βη-≡ t


-- Congruences of βη-≡

equiv : ∀ {Γ σ} → {t₁ t₂ : Tm Γ σ} → t₁ ≡ t₂ → t₁ βη-≡ t₂
equiv refl = brefl


congSubstVar : ∀ {σ Γ τ} → (v : Var Γ τ) → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) σ} → u₁ βη-≡ u₂ → substVar v x u₁ βη-≡ substVar v x u₂
congSubstVar v x p with eq x v
congSubstVar v .v p | same = p
congSubstVar .(wkv v x) .v p | diff v x = brefl


congWkTm : ∀ {Γ σ τ} → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) τ} → u₁ βη-≡ u₂ → wkTm x u₁ βη-≡ wkTm x u₂
congWkTm _ brefl = brefl
congWkTm x (bsym p) = bsym (congWkTm x p)
congWkTm x (btrans p₁ p₂) = btrans (congWkTm x p₁) (congWkTm x p₂)
congWkTm x (congΛ p) = congΛ (congWkTm (vs x) p)
congWkTm x (congApp p₁ p₂) = congApp (congWkTm x p₁) (congWkTm x p₂)
congWkTm x {app (Λ t) u} beta = btrans beta (equiv (sym (wkTmSubstExc (vs x) t vz u)))
congWkTm x {._} {t} eta = btrans (congΛ (congApp (equiv (wkTmExc vz x t)) brefl)) eta


congSubst : ∀ {σ Γ τ} → (t : Tm Γ τ) → (x : Var Γ σ) → {u₁ u₂ : Tm (Γ - x) σ} → u₁ βη-≡ u₂ → hsubst.subst t x u₁ βη-≡ hsubst.subst t x u₂
congSubst (var v) x p = congSubstVar v x p
congSubst (Λ t) x p = congΛ (congSubst t (vs x) (congWkTm vz p))
congSubst (app t₁ t₂) x p = congApp (congSubst t₁ x p) (congSubst t₂ x p)


congEmbSp : ∀ {Γ σ τ} → (us : Sp Γ σ τ) → {acc₁ acc₂ : Tm Γ σ} → acc₁ βη-≡ acc₂ → embSp us acc₁ βη-≡ embSp us acc₂
congEmbSp ε p = p
congEmbSp (u , us) p = congEmbSp us (congApp p brefl)


-- -- Proofs that involve with

substSame : ∀ {Γ σ} → (x : Var Γ σ) → (u : Tm (Γ - x) σ) → eq x x ≡ same → u βη-≡ substVar x x u
substSame x u p with eq x x
substSame x u refl | .same = brefl


substDiff : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (u : Tm (Γ - x) σ) → eq x (wkv x y) ≡ diff x y → var y βη-≡ substVar (wkv x y) x u
substDiff x y u p with eq x (wkv x y)
substDiff x y u refl | .(diff x y) = brefl


-- Proofs


mutual

  -- wkNf and wkTm act similar

  wkNfTm : ∀ {Γ σ τ} → (x : Var Γ σ) → (u : Nf (Γ - x) τ) → ⌈ wkNf x u ⌉ βη-≡ wkTm x ⌈ u ⌉
  wkNfTm x (λn t)        = congΛ (wkNfTm (vs x) t)
  wkNfTm x (ne (y , us)) = wkSpTm x us (var y)


  -- wkSp and wkTm act similar

  wkSpTm : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (ns : Sp (Γ - x) τ ρ) → (acc : Tm (Γ - x) τ) → embSp (wkSp x ns) (wkTm x acc) βη-≡ wkTm x (embSp ns acc)
  wkSpTm x ε _ = brefl
  wkSpTm x (u , us) acc = btrans (congEmbSp (wkSp x us) (congApp brefl (wkNfTm x u))) (wkSpTm x us (app acc ⌈ u ⌉))


-- The way the accumulator works with Sp

accSp : ∀ {Γ σ τ ρ} → (ts : Sp Γ ρ (σ ⇒ τ)) → (u : Nf Γ σ) → (acc : Tm Γ ρ) → embSp (appSp ts u) acc βη-≡ embSp (u , ε) (embSp ts acc)
accSp ε u acc = brefl
accSp (t , ts) u acc = accSp ts u (app acc ⌈ t ⌉)


mutual

  -- Embedding the normal form of a Ne is βη-equivalent to embedding the Ne

  compNe : ∀ {σ Γ} → (n : Ne Γ σ) → ⌈ ne2nf n ⌉ βη-≡ embNe n
  compNe {○} xns = brefl
  compNe {σ ⇒ τ} (x , ns) = btrans
                             (congΛ
                              (btrans (compNe (vs x , appSp (wkSp vz ns) (ne2nf (vz , ε))))
                               (btrans (accSp (wkSp vz ns) (nvar vz) (var (vs x)))
                                (congApp (wkSpTm vz ns (var x)) (compVar vz)))))
                             eta


  -- Embedding the normal form of a variable is βη-equivalent to the variable

  compVar : ∀ {σ Γ} → (v : Var Γ σ) → ⌈ nvar v ⌉ βη-≡ var v
  compVar v = compNe (v , ε)


mutual

  -- How to distribute substitution in embSp

  substEmbSp : ∀ {Γ σ τ ρ} → (ts : Sp Γ τ ρ) → (x : Var Γ σ) → (t : Nf (Γ - x) σ) → (acc : Tm Γ τ) → embSp (ts < x := t >) (hsubst.subst acc x ⌈ t ⌉) βη-≡ hsubst.subst (embSp ts acc) x ⌈ t ⌉
  substEmbSp ε        x u acc = brefl
  substEmbSp (t , ts) x u acc = btrans
                                 (congEmbSp (ts < x := u >) (congApp brefl (substNfSubst t x u)))
                                 (substEmbSp ts x u (app acc ⌈ t ⌉))


  -- ⌈ ◇ ⌉ is like embSp thanks to the accumulator

  appNfEmbSp : ∀ {Γ σ} → (u : Nf Γ σ) → (ts : Sp Γ σ ○) → ⌈ u ◇ ts ⌉ βη-≡ embSp ts ⌈ u ⌉
  appNfEmbSp u ε = brefl
  appNfEmbSp u (t , ts) = btrans (appNfEmbSp (napp u t) ts) (congEmbSp ts (compApp u t))


  -- •[•:=•] and subst act similar

  substNfSubst : ∀ {σ Γ τ} → (t : Nf Γ τ) → (x : Var Γ σ) → (u : Nf (Γ - x) σ) → ⌈ t [ x := u ] ⌉ βη-≡ hsubst.subst ⌈ t ⌉ x ⌈ u ⌉
  substNfSubst (λn t) x u = congΛ
                             (btrans (substNfSubst t (vs x) (wkNf vz u))
                              (congSubst ⌈ t ⌉ (vs x) (wkNfTm vz u)))
  substNfSubst (ne (y , ts))          x u with eq x y
  substNfSubst (ne (x , ts))         .x u | same  = btrans
                                                      (btrans (appNfEmbSp u (ts < x := u >))
                                                       (congEmbSp (ts < x := u >) (substSame x ⌈ u ⌉ (substSame3 x))))
                                                      (substEmbSp ts x u (var x))
  substNfSubst (ne (.(wkv x y), ts)) .x u | diff x y = btrans
                                                        (congEmbSp (ts < x := u >) (substDiff x y ⌈ u ⌉ (substDiff3 x y)))
                                                        (substEmbSp ts x u (var (wkv x y)))


  -- Embedding an application is the application of embedded terms

  compApp : ∀ {Γ σ τ} → (t₁ : Nf Γ (σ ⇒ τ)) → (t₂ : Nf Γ σ) → ⌈ napp t₁ t₂ ⌉ βη-≡ app ⌈ t₁ ⌉ ⌈ t₂ ⌉
  compApp (λn t) u = btrans (substNfSubst t vz u) (bsym beta)


-- Completeness

completeness : ∀ {σ Γ} → (t : Tm Γ σ) → ⌈ nf t ⌉ βη-≡ t
completeness (var v) = compVar v
completeness (Λ t) = congΛ (completeness t)
completeness (app t₁ t₂) = btrans (compApp (nf t₁) (nf t₂))
                            (congApp (completeness t₁) (completeness t₂))


-- A consequence of completeness

convertnf : ∀ {Γ σ} → (t u : Tm Γ σ) → nf t ≡ nf u → t βη-≡ u
convertnf t u h = btrans (bsym (completeness t))
                    (btrans (equiv (cong ⌈_⌉ h)) (completeness u))


-- .


mutual

  -- wkSp and appSp commute

  wkSpAppSp : ∀ {Γ σ τ ρ α} → (x : Var Γ σ) → (ts : Sp (Γ - x) τ (ρ ⇒ α)) → wkSp (vs x) (appSp (wkSp vz ts) (nvar vz)) ≡ appSp (wkSp vz (wkSp x ts)) (nvar vz)
  wkSpAppSp x ε = cong (λ u → (u , ε)) (ne2nfWkNf (vs x) vz ε)
  wkSpAppSp x (t , ts) = cong₂ (λ u us → (u , us)) (wkNfExc vz x t) (wkSpAppSp x ts)


  -- wkNf and ne2nf commute

  ne2nfWkNf : ∀ {ρ Γ σ τ} → (x : Var Γ σ) → (v : Var (Γ - x) τ) → (ts : Sp (Γ - x) τ ρ) → wkNf x (ne2nf (v , ts)) ≡ ne2nf (wkv x v , wkSp x ts)
  ne2nfWkNf {○} x v ts = refl
  ne2nfWkNf {σ ⇒ τ} x v ts = begin
    _ ≡⟨ cong λn (ne2nfWkNf (vs x) (vs v) (appSp (wkSp vz ts) (nvar vz))) ⟩
    _ ≡⟨ cong (λ u → λn (ne2nf (vs (wkv x v) , u))) (wkSpAppSp x ts) ⟩
    _ ∎


-- nf ans wk commute

nfWkNfWkTm : ∀ {Γ σ τ} → (x : Var Γ σ) → (u : Tm (Γ - x) τ) → wkNf x (nf u) ≡ nf (wkTm x u)
nfWkNfWkTm x (var v) = ne2nfWkNf x v ε
nfWkNfWkTm x (Λ t) = cong λn (nfWkNfWkTm (vs x) t)
nfWkNfWkTm x (app t₁ t₂) = begin
  _ ≡⟨ nappWkNf x (nf t₁) (nf t₂) ⟩
  _ ≡⟨ cong₂ napp (nfWkNfWkTm x t₁) (nfWkNfWkTm x t₂) ⟩
  _ ∎


-- ◇ and app commute

appNfSpNapp : ∀ {Γ σ τ ρ} → (u : Nf Γ σ) → (ts : Sp Γ σ (τ ⇒ ρ)) → (t : Nf Γ τ) → u ◇ (appSp ts t) ≡ napp (u ◇ ts) t
appNfSpNapp u ε t = refl
appNfSpNapp u (t₁ , ts₁) t = appNfSpNapp (napp u t₁) ts₁ t


-- subst and appSp comute

substAppSp : ∀ {Γ σ τ ρ α} → (ts : Sp Γ σ (τ ⇒ ρ)) → (t : Nf Γ τ) → (x : Var Γ α) → (u : Nf (Γ - x) α) → (appSp ts t) < x := u > ≡ appSp (ts < x := u >) (t [ x := u ])
substAppSp ε t x u = refl
substAppSp (t₁ , ts₁) t x u = cong (λ us → (t₁ [ x := u ]) , us) (substAppSp ts₁ t x u)


-- Substitution in ne2nf

ne2nfSubstAux : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (ts : Sp Γ τ ○) → (u : Nf (Γ - x) σ) → eq x (wkv x y) ≡ diff x y → (ne2nf (wkv x y , ts)) [ x := u ] ≡ ne2nf (y , (ts < x := u >))
ne2nfSubstAux x y ts u p with eq x (wkv x y)
ne2nfSubstAux x y ts u refl | .(diff x y) = refl


mutual

  ne2nfSubst : ∀ {ρ Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (ts : Sp Γ τ ρ) → (u : Nf (Γ - x) σ) → (ne2nf (wkv x y , ts)) [ x := u ] ≡ ne2nf (y , (ts < x := u >))
  ne2nfSubst {○} x y ts u = ne2nfSubstAux x y ts u (substDiff3 x y)
  ne2nfSubst {σ ⇒ τ} x y ts u = begin
    _ ≡⟨ cong λn (ne2nfSubst (vs x) (vs y) (appSp (wkSp vz ts) (nvar vz)) (wkNf vz u)) ⟩
    _ ≡⟨ cong (λ us → λn (ne2nf (vs y , us))) (weakSubstSpApp ts x u) ⟩
    _ ∎


  -- Weakening and •<•:=•>

  weakSubstSpApp : ∀ {Γ σ τ ρ α} → (ts : Sp Γ σ (τ ⇒ α)) → (x : Var Γ ρ) → (u : Nf (Γ - x) ρ) → (appSp (wkSp vz ts) (nvar vz)) < (vs x) := (wkNf vz u) > ≡ appSp (wkSp vz (ts < x := u >)) (nvar vz)
  weakSubstSpApp ts x u = begin
    _ ≡⟨ substAppSp (wkSp vz ts) (nvar vz) (vs x) (wkNf vz u) ⟩
    _ ≡⟨ cong₂ (λ us us' → appSp us us') (sym (wkSpSubstSpExc vz ts x u)) (ne2nfSubst (vs x) vz ε (wkNf vz u)) ⟩
    _ ∎


-- Concatenation of Sp

concatSp : ∀ {Γ σ τ ρ} → Sp Γ σ τ → Sp Γ τ ρ → Sp Γ σ ρ
concatSp ε us = us
concatSp (t , ts) us = t , concatSp ts us


-- Concatenation on the right

concat1 : ∀ {Γ σ τ} → (ts : Sp Γ σ τ) → concatSp ts ε ≡ ts
concat1 ε = refl
concat1 (t , ts) = cong (λ us → (t , us)) (concat1 ts)


concat2 : ∀ {Γ σ τ ρ α} → (ts : Sp Γ σ (τ ⇒ ρ)) → (u : Nf Γ τ) → (us : Sp Γ ρ α) → concatSp ts (u , us) ≡ concatSp (appSp ts u) us
concat2 ε _ _ = refl
concat2 (t , ts) u us = cong (λ us' → t , us') (concat2 ts u us)


-- Substitution in ne2nf

ne2nfAppNfAux : ∀ {Γ σ} → (x : Var Γ σ) → (ts : Sp Γ σ ○) → (u : Nf (Γ - x) σ) → eq x x ≡ same → (ne2nf (x , ts)) [ x := u ] ≡ u ◇ (ts < x := u >)
ne2nfAppNfAux x ts u p with eq x x
ne2nfAppNfAux x ts u refl | .same = refl



mutual

  -- ◇, ne2nf and concatSp
  -- solve proving etaEq

  appNfNe2nfConcat : ∀ {Γ σ τ} → (x : Var Γ σ) → (ts : Sp Γ σ τ) → (us : Sp Γ τ ○) → (ne2nf (x , ts)) ◇ us ≡ ne (x , concatSp ts us)
  appNfNe2nfConcat x ts ε = cong (λ us → ne (x , us)) (sym (concat1 ts))
  appNfNe2nfConcat x ts (u , us) = begin
    _ ≡⟨ cong (λ t → t ◇ us) (ne2nfSubst vz x (appSp (wkSp vz ts) (nvar vz)) u) ⟩
    _ ≡⟨ cong (λ t → ne2nf (x , t) ◇ us) (substAppSp (wkSp vz ts) (nvar vz) vz u) ⟩
    _ ≡⟨ cong₂ (λ t t' → ne2nf (x , appSp t t') ◇ us) (weakSubstSp vz ts u) (ne2nfAppNf vz ε u) ⟩
    _ ≡⟨ appNfNe2nfConcat x (appSp ts u) us ⟩
    _ ≡⟨ cong (λ t → ne (x , t)) (sym (concat2 ts u us)) ⟩
    _ ∎


  substNfNe : ∀ {Γ σ τ} → (i : Var Γ τ) → (x : Var (Γ - i) σ) → (xs : Sp (Γ - i) σ ○) → (j : Var Γ τ) → (k : Var (Γ - j) τ) → (p : onediff j i) → (l : Var Γ σ) → l ≡ wkv i x → wkv i (! sym (onediffMinus i j p) >₀ k) ≡ j → (ne (l , wkSp i xs)) [ j := (nvar k) ] ≡ ne ((! onediffMinus i j p >₀ x) , (! onediffMinus i j p >₃ xs))
  substNfNe i x xs j k s l q r with eq j l
  substNfNe i x xs j k s .j q r          | same = begin
    _ ≡⟨ appNfNe2nfConcat k ε (wkSp i xs < j := ne2nf (k , ε) >) ⟩
    _ ≡⟨ cong (λ v → ne (v , (wkSp i xs < j := ne2nf (k , ε) >))) (!! x k (onediffMinus i j s) (sym (wkvInj i (! sym (onediffMinus i j s) >₀ k) x (trans r q)))) ⟩
    _ ≡⟨ cong (λ us → ne ((! onediffMinus i j s >₀ x) , us)) (substNfSp i j xs k s r) ⟩
    _ ∎
  substNfNe i x xs .j k s .(wkv j z) q r | diff j z = cong₂ (λ v us → ne (v , us)) (onediffWkv i j z x s q) (substNfSp i j xs k s r)


  substNfSp : ∀ {Γ σ τ ρ} → (i j : Var Γ σ) → (xs : Sp (Γ - i) ρ τ) → (k : Var (Γ - j) σ) → (p : onediff j i) → wkv i (! sym (onediffMinus i j p) >₀ k) ≡ j → (wkSp i xs) < j := (nvar k) > ≡ ! onediffMinus i j p >₃ xs
  substNfSp i j ε k r q = sym (!ε (onediffMinus i j r))
  substNfSp i j (n , xs) k r q = begin
    _ ≡⟨ cong₂ (λ a b → a , b) (substNfEq i n j k r q) (substNfSp i j xs k r q) ⟩
    _ ≡⟨ sym (!, (onediffMinus i j r) n xs) ⟩
    _ ∎


  substNfEq : ∀ {σ Γ τ} → (i : Var Γ τ) → (n : Nf (Γ - i) σ) → (j : Var Γ τ) → (k : Var (Γ - j) τ) → (p : onediff j i) → wkv i (! sym (onediffMinus i j p) >₀ k) ≡ j → (wkNf i n) [ j := (nvar k) ] ≡ ! onediffMinus i j p >₂ n
  substNfEq {σ ⇒ τ} i (λn n) j k r q = begin
    _ ≡⟨ cong (λ u → λn (wkNf (vs i) n [ vs j := u ])) (ne2nfWkNf vz k ε) ⟩
    _ ≡⟨ cong λn (substNfEq (vs i) n (vs j) (vs k) (ods j i r) (trans (cong (wkv (vs i)) (!p (vs {σ} k) (sym (cong (λ Θ → Θ , σ) (onediffMinus i j r))) (cong (λ Θ → Θ , σ) (sym (onediffMinus i j r))) (reflExtConSym _ (onediffMinus i j r)))) (trans (cong (wkv (vs i)) (!vs (sym (onediffMinus i j r)) k)) (cong vs q)))) ⟩
    _ ≡⟨ (sym (!λn (onediffMinus i j r) n)) ⟩
    _ ∎
  substNfEq i (ne (x , xs)) j k r q = begin
    _ ≡⟨ substNfNe i x xs j k r (wkv i x) refl q ⟩
    _ ≡⟨ sym (!ne (onediffMinus i j r) x xs) ⟩
    _ ∎


  etaEq : ∀ {σ Γ τ} → (u : Nf Γ (σ ⇒ τ)) → λn (napp (wkNf vz u) (nvar vz)) ≡ u
  etaEq (λn u) = cong λn (substNfEq (vs vz) u vz vz odz refl)


  ne2nfAppNf : ∀ {τ Γ σ} → (x : Var Γ σ) → (ts : Sp Γ σ τ) → (u : Nf (Γ - x) σ) → (ne2nf (x , ts)) [ x := u ] ≡ u ◇ (ts < x := u >)
  ne2nfAppNf {○} x ts u = ne2nfAppNfAux x ts u (substSame3 x)
  ne2nfAppNf {σ ⇒ τ} x ts u = begin
    _ ≡⟨ cong λn (ne2nfAppNf (vs x) (appSp (wkSp vz ts) (nvar vz)) (wkNf vz u)) ⟩
    _ ≡⟨ cong (λ us → λn (wkNf vz u ◇ us)) (weakSubstSpApp ts x u) ⟩
    _ ≡⟨ cong λn (appNfSpNapp (wkNf vz u) (wkSp vz (ts < x := u >)) (nvar vz)) ⟩
    _ ≡⟨ cong (λ t → λn (napp t (ne2nf (vz , ε)))) (appNfWkNfSp vz u (ts < x := u >)) ⟩
    _ ≡⟨ etaEq (u ◇ (ts < x := u >)) ⟩
    _ ∎


-- nf and •[•:=•] commute

nfSubstNf : ∀ {Γ σ τ} → (t : Tm Γ τ) → (x : Var Γ σ) → (u : Tm (Γ - x) σ) → (nf t) [ x := (nf u) ] ≡ nf (hsubst.subst t x u)
nfSubstNf (var v) x u with eq x v
nfSubstNf (var x) .x u | same = ne2nfAppNf x ε (nf u)
nfSubstNf (var .(wkv x v)) .x u | diff x v = ne2nfSubst x v ε (nf u)
nfSubstNf (Λ t) x u = begin
  _ ≡⟨ cong (λ a → λn (nf t [ vs x := a ])) (nfWkNfWkTm vz u) ⟩
  _ ≡⟨ cong λn (nfSubstNf t (vs x) (wkTm vz u)) ⟩
  _ ∎
nfSubstNf (app t₁ t₂) x u = begin
  _ ≡⟨ substNfNapp (nf t₁) (nf t₂) x (nf u) ⟩
  _ ≡⟨ cong₂ napp (nfSubstNf t₁ x u) (nfSubstNf t₂ x u) ⟩
  _ ∎


-- Soundness

soundness : ∀ {Γ σ} → {t u : Tm Γ σ} → t βη-≡ u → nf t ≡ nf u
soundness brefl = refl
soundness (bsym p) = sym (soundness p)
soundness (btrans p₁ p₂) = trans (soundness p₁) (soundness p₂)
soundness (congΛ p) = cong λn (soundness p)
soundness (congApp p₁ p₂) = cong₂ napp (soundness p₁) (soundness p₂)
soundness {_} {_} {app (Λ t) u} beta = nfSubstNf t vz u
soundness {_} {._} {._} {t} eta = begin
  _ ≡⟨ cong (λ u → λn (napp u (ne2nf (vz , ε)))) (sym (nfWkNfWkTm vz t)) ⟩
  _ ≡⟨ etaEq (nf t) ⟩
  _ ∎


-- .


mutual

  -- nf, embSp and ◇

  nfEmbSpAppNf : ∀ {Γ σ} → (ts : Sp Γ σ ○) → (acc : Tm Γ σ) → nf (embSp ts acc) ≡ (nf acc) ◇ ts
  nfEmbSpAppNf ε acc = refl
  nfEmbSpAppNf (t , ts) acc = begin
    _ ≡⟨ nfEmbSpAppNf ts (app acc ⌈ t ⌉) ⟩
    _ ≡⟨ cong (λ u → napp (nf acc) u ◇ ts) (stability t) ⟩
    _ ∎


  -- Stability

  stability : ∀ {Γ σ} → (u : Nf Γ σ) → nf ⌈ u ⌉ ≡ u
  stability (λn u) = cong λn (stability u)
  stability (ne (x , ts)) = begin
    _ ≡⟨ nfEmbSpAppNf ts (var x) ⟩
    _ ≡⟨ appNfNe2nfConcat x ε ts ⟩
    _ ∎

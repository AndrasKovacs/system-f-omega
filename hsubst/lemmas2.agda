--------------------------------------------------------------------------------
-- This module implements basic commutation lemmas for variables, terms and   --
-- normal forms, about weakening and removal of variables from contexts.      --
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

module lemmas2 where


open import hsubst
open import lemmas1

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


-- Exchanging two variable removals from a context

rem : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → Var (Γ - (wkv x y)) σ
rem vz _ = vz
rem (vs x) vz = x
rem (vs x) (vs y) = vs (rem x y)


-- Lemmas about rem

conExc : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (Γ - x) - y ≡ (Γ - (wkv x y)) - (rem x y)
conExc vz y = refl
conExc (vs x) vz = refl
conExc (vs {σ} x) (vs y) = cong (λ Θ → Θ , σ) (conExc x y)


wkRem : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → wkv (wkv x y) (rem x y) ≡ x
wkRem vz _ = refl
wkRem (vs _) vz = refl
wkRem (vs x) (vs y) = cong vs (wkRem x y)


wkvExc : ∀ {ρ Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (v : Var ((Γ - x) - y) ρ) → wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ wkv x (wkv y v)
wkvExc vz _ _ = refl
wkvExc (vs x) vz _ = refl
wkvExc (vs x) (vs y) vz =  cong (λ v → wkv (vs (wkv x y)) (wkv (vs (rem x y)) v)) (!vz (conExc x y))
wkvExc (vs x) (vs y) (vs v) = begin
  _ ≡⟨ cong (λ z → wkv (vs (wkv x y)) (wkv (vs (rem x y)) z)) (!vs (conExc x y) v) ⟩
  _ ≡⟨ cong vs (wkvExc x y v) ⟩
  _ ∎


wkTmExc : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (t : Tm ((Γ - x) - y) ρ) → wkTm (wkv x y) (wkTm (rem x y) (! conExc x y >₁ t)) ≡ wkTm x (wkTm y t)
wkTmExc x y (var v) = begin
  _ ≡⟨ cong (λ t → wkTm (wkv x y) (wkTm (rem x y) t)) (!var (conExc x y) v) ⟩
  _ ≡⟨ cong var (wkvExc x y v) ⟩
  _ ∎
wkTmExc x y (Λ t) = begin
  _ ≡⟨ cong (λ u → wkTm (wkv x y) (wkTm (rem x y) u)) (!Λ (conExc x y) t) ⟩
  _ ≡⟨ cong Λ (wkTmExc (vs x) (vs y) t) ⟩
  _ ∎
wkTmExc x y (app t₁ t₂) = begin
  _ ≡⟨ cong (λ t → wkTm (wkv x y) (wkTm (rem x y) t)) (!app (conExc x y) t₁ t₂) ⟩
  _ ≡⟨ cong₂ app (wkTmExc x y t₁) (wkTmExc x y t₂) ⟩
  _ ∎


mutual

  wkNfExc : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (t : Nf ((Γ - x) - y) ρ) → wkNf (wkv x y) (wkNf (rem x y) (! conExc x y >₂ t)) ≡ wkNf x (wkNf y t)
  wkNfExc x y (λn t) = begin
    _ ≡⟨ cong (λ u → wkNf (wkv x y) (wkNf (rem x y) u)) (!λn (conExc x y) t) ⟩
    _ ≡⟨ cong λn (wkNfExc (vs x) (vs y) t) ⟩
    _ ∎
  wkNfExc x y (ne (v , ts)) = begin
    _ ≡⟨ cong (λ t → wkNf (wkv x y) (wkNf (rem x y) t)) (!ne (conExc x y) v ts) ⟩
    _ ≡⟨ cong₂ (λ z us → ne (z , us)) (wkvExc x y v) (wkSpExc x y ts) ⟩
    _ ∎


  wkSpExc : ∀ {Γ σ τ ρ α} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → (ts : Sp ((Γ - x) - y) ρ α) → wkSp (wkv x y) (wkSp (rem x y) (! conExc x y >₃ ts)) ≡ wkSp x (wkSp y ts)
  wkSpExc x y ε = cong (λ ts → wkSp (wkv x y) (wkSp (rem x y) ts)) (!ε (conExc x y))
  wkSpExc x y (t , ts) = begin
    _ ≡⟨ cong (λ us → wkSp (wkv x y) (wkSp (rem x y) us)) (!, (conExc x y) t ts) ⟩
    _ ≡⟨ cong₂ (λ u us → u , us) (wkNfExc x y t) (wkSpExc x y ts) ⟩
    _ ∎


wkvSubstExtAux1 : ∀ {Γ σ τ} → (y : Var Γ σ) → (v : Var (Γ - y) τ) → (u : Tm ((Γ - y) - v) τ) → eq (wkv y v) (wkv y v) ≡ same → wkTm (rem y v) (! conExc y v >₁ u) ≡ substVar (wkv y v) (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))
wkvSubstExtAux1 y v u p with eq (wkv y v) (wkv y v)
wkvSubstExtAux1 y v u refl | .same = refl


wkvSubstExtAux2 : ∀ {Γ σ τ ρ} → (y : Var Γ σ) → (v : Var (Γ - y) ρ) → (z : Var ((Γ - y) - v) τ) → (u : Tm ((Γ - y) - v) ρ) → eq (wkv y v) (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) ≡ diff (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)) → wkTm (rem y v) (! conExc y v >₁ var z) ≡ substVar (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)))
  (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))
wkvSubstExtAux2 y v z u p with eq (wkv y v) (wkv (wkv y v) (wkv (rem y v) (! conExc y v >₀ z)))
wkvSubstExtAux2 y v z u refl
  | .(diff (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) = (cong (wkTm (rem y v)) (!var (conExc y v) z))


wkvSubstExt : ∀ {Γ σ τ ρ} → (y : Var Γ σ) → (v : Var (Γ - y) τ) → (x : Var (Γ - y) ρ) → (u : Tm ((Γ - y) - x) ρ) → wkTm (rem y x) (! conExc y x >₁ (substVar v x u)) ≡ substVar (wkv y v) (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkvSubstExt y v x u with eq x v
wkvSubstExt y v .v u | same = wkvSubstExtAux1 y v u (substSame3 (wkv y v))
wkvSubstExt y .(wkv v z) .v u | diff v z = begin
  _ ≡⟨ wkvSubstExtAux2 y v z u (substDiff3 (wkv y v) (wkv (rem y v) (! conExc y v >₀ z))) ⟩
  _ ≡⟨ cong (λ a → substVar a (wkv y v) (wkTm (rem y v) (! conExc y v >₁ u))) (wkvExc y v z) ⟩
  _ ∎


wkTmSubstExc : ∀ {Γ σ τ ρ} → (y : Var Γ σ) → (t : Tm (Γ - y) τ) → (x : Var (Γ - y) ρ) → (u : Tm ((Γ - y) - x) ρ) → wkTm (rem y x) (! conExc y x >₁ (hsubst.subst t x u)) ≡ hsubst.subst (wkTm y t) (wkv y x) (wkTm (rem y x) (! conExc y x >₁ u))
wkTmSubstExc y (var v) x u = wkvSubstExt y v x u
wkTmSubstExc y (Λ t) x u = begin
  _ ≡⟨ cong (wkTm (rem y x)) (!Λ (conExc y x) (hsubst.subst t (vs x) (wkTm vz u))) ⟩
  _ ≡⟨ cong Λ (wkTmSubstExc (vs y) t (vs x) (wkTm vz u)) ⟩
  _ ≡⟨ cong (λ n → Λ (hsubst.subst (wkTm (vs y) t) (vs (wkv y x)) (wkTm (vs (rem y x)) n))) (!wkTm (conExc y x) u) ⟩
  _ ≡⟨ cong (λ n → Λ (hsubst.subst (wkTm (vs y) t) (vs (wkv y x)) n)) (wkTmExc vz (rem y x) (! conExc y x >₁ u)) ⟩
  _ ∎
wkTmSubstExc y (app t₁ t₂) x u = begin
  _ ≡⟨ cong (wkTm (rem y x)) (!app (conExc y x) (hsubst.subst t₁ x u) (hsubst.subst t₂ x u)) ⟩
  _ ≡⟨ cong₂ app (wkTmSubstExc y t₁ x u) (wkTmSubstExc y t₂ x u) ⟩
  _ ∎


mutual

  -- wkNf and napp commute

  nappWkNf : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (t₁ : Nf (Γ - x) (τ ⇒ ρ)) → (t₂ : Nf (Γ - x) τ) → wkNf x (napp t₁ t₂) ≡ napp (wkNf x t₁) (wkNf x t₂)
  nappWkNf x (λn t) u = {!wkNfSubstNfExc!} -- wkNfSubstNfExc (vs x) t vz u


  -- ◇ and wk commute

  appNfWkNfSp : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (u : Nf (Γ - x) τ) → (ts : Sp (Γ - x) τ ρ) → (wkNf x u) ◇ (wkSp x ts) ≡ wkNf x (u ◇ ts)
  appNfWkNfSp x u ε = refl
  appNfWkNfSp x u (t , ts) = begin
    _ ≡⟨ cong (λ n → n ◇ wkSp x ts) (sym (nappWkNf x u t)) ⟩
    _ ≡⟨ appNfWkNfSp x (napp u t) ts ⟩
    _ ∎


  wkNfSubstNfExcAux1 : ∀ {Γ σ τ} → (y : Var Γ σ) → (ts : Sp (Γ - y) τ ○) → (x : Var (Γ - y) τ) → (u : Nf ((Γ - y) - x) τ) → eq (wkv y x) (wkv y x) ≡ same → wkNf (rem y x) (! conExc y x >₂ (u ◇ (ts < x := u >))) ≡ (ne (wkv y x , wkSp y ts)) [ (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) ]
  wkNfSubstNfExcAux1 y ts x u p with eq (wkv y x) (wkv y x)
  wkNfSubstNfExcAux1 y ts x u refl | .same = begin
    _ ≡⟨ cong (wkNf (rem y x)) (!appNf (conExc y x) u (ts < x := u >)) ⟩
    _ ≡⟨ sym (appNfWkNfSp (rem y x) (! conExc y x >₂ u) (! conExc y x >₃ (ts < x := u >))) ⟩
    _ ≡⟨ cong (λ n → wkNf (rem y x) (! conExc y x >₂ u) ◇ n) (wkSpSubstSpExc y ts x u) ⟩
    _ ∎


  wkNfSubstNfExcAux2 : ∀ {Γ σ τ ρ} → (y : Var Γ σ) → (ts : Sp (Γ - y) τ ○) → (x : Var (Γ - y) ρ) → (u : Nf ((Γ - y) - x) ρ) → (v : Var ((Γ - y) - x) τ) → eq (wkv y x) (wkv (wkv y x) (wkv (rem y x) (! conExc y x >₀ v))) ≡ diff (wkv y x) (wkv (rem y x) (! conExc y x >₀ v)) → wkNf (rem y x) (! conExc y x >₂ ne (v , (ts < x := u >))) ≡ (ne (wkv (wkv y x) (wkv (rem y x) (! conExc y x >₀ v)) , wkSp y ts)) [ (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) ]
  wkNfSubstNfExcAux2 y ts x u v p with eq (wkv y x) (wkv (wkv y x) (wkv (rem y x) (! conExc y x >₀ v)))
  wkNfSubstNfExcAux2 y ts x u v refl | .(diff (wkv y x) (wkv (rem y x) (! conExc y x >₀ v))) = begin
    _ ≡⟨ cong (wkNf (rem y x)) (!ne (conExc y x) v (ts < x := u >)) ⟩
    _ ≡⟨ cong (λ us → ne (wkv (rem y x) (! conExc y x >₀ v) , us)) (wkSpSubstSpExc y ts x u) ⟩
    _ ∎


  wkNfSubstNfExc : ∀ {Γ σ τ ρ} → (y : Var Γ σ) → (t : Nf (Γ - y) τ) → (x : Var (Γ - y) ρ) → (u : Nf ((Γ - y) - x) ρ) → wkNf (rem y x) (! conExc y x >₂ (t [ x := u ])) ≡ (wkNf y t) [ (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) ]
  wkNfSubstNfExc y (λn t) x u = begin
    _ ≡⟨ cong (wkNf (rem y x)) (!λn (conExc y x) (t [ (vs x) := (wkNf vz u) ])) ⟩
    _ ≡⟨ cong λn (wkNfSubstNfExc (vs y) t (vs x) (wkNf vz u)) ⟩
    _ ≡⟨ cong (λ n → λn (wkNf (vs y) t [ vs (wkv y x) := wkNf (vs (rem y x)) n ])) (!wkNf (conExc y x) u) ⟩
    _ ≡⟨ cong (λ n → λn (wkNf (vs y) t [ vs (wkv y x) := n ])) (wkNfExc vz (rem y x) (! conExc y x >₂ u)) ⟩
    _ ∎
  wkNfSubstNfExc y (ne (v , ts)) x u with eq x v
  wkNfSubstNfExc y (ne (x , ts)) .x u | same = wkNfSubstNfExcAux1 y ts x u (substSame3 (wkv y x))
  wkNfSubstNfExc y (ne (.(wkv x v) , ts)) .x u | diff x v = begin
    _ ≡⟨ wkNfSubstNfExcAux2 y ts x u v (substDiff3 (wkv y x) (wkv (rem y x) (! conExc y x >₀ v))) ⟩
    _ ≡⟨ cong (λ z → ne (z , wkSp y ts) [ wkv y x := wkNf (rem y x) (! conExc y x >₂ u) ]) (wkvExc y x v) ⟩
    _ ∎


  wkSpSubstSpExc : ∀ {Γ σ τ ρ α} → (y : Var Γ σ) → (ts : Sp (Γ - y) τ ρ) → (x : Var (Γ - y) α) → (u : Nf ((Γ - y) - x) α) → wkSp (rem y x) (! conExc y x >₃ (ts < x := u >)) ≡ (wkSp y ts) < (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) >
  wkSpSubstSpExc y ε x u = cong (wkSp (rem y x)) (!ε (conExc y x))
  wkSpSubstSpExc y (t , ts) x u = begin
    _ ≡⟨ cong (wkSp (rem y x)) (!, (conExc y x) (t [ x := u ]) (ts < x := u >)) ⟩
    _ ≡⟨ cong₂ (λ n us → n , us) (wkNfSubstNfExc y t x u) (wkSpSubstSpExc y ts x u) ⟩
    _ ∎

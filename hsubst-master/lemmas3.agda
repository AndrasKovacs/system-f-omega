--------------------------------------------------------------------------------
-- This modules implements basic commutation lemmas between hereditary        --
-- substitutions and other operations on normal forms such as weakening.      --
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

module lemmas3 where


open import hsubst
open import lemmas1
open import lemmas2

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


-- weakening and substitution: (t+x)[x:=u] = t (for t variable, term or
-- normal form)

weakSubstAux : ∀ {Γ σ τ} -> (x : Var Γ τ) -> (v : Var (Γ - x) σ) -> (u : Tm (Γ - x) τ) -> eq x (wkv x v) ≡ diff x v -> substVar (wkv x v) x u ≡ var v
weakSubstAux x v u p with eq x (wkv x v)
weakSubstAux x v u refl | .(diff x v) = refl


weakSubst : ∀ {Γ σ τ} -> (x : Var Γ τ) -> (t : Tm (Γ - x) σ) -> (u : Tm (Γ - x) τ) -> hsubst.subst (wkTm x t) x u ≡ t
weakSubst x (var v) u = weakSubstAux x v u (substDiff3 x v)
weakSubst x (Λ t) u = cong Λ (weakSubst (vs x) t (wkTm vz u))
weakSubst x (app t₁ t₂) u = cong₂ app (weakSubst x t₁ u) (weakSubst x t₂ u)


-- Commutation lemmas between substVar and rem, wkv

substVarCommAux2 : ∀ {Γ σ τ} -> (x : Var Γ σ) -> (u₁ : Tm (Γ - x) σ) -> (y : Var (Γ - x) τ) -> (u₂ : Tm ((Γ - x) - y) τ) -> eq (rem x y) (rem x y) ≡ same -> ! conExc x y >₁ hsubst.subst u₁ y u₂ ≡ substVar (rem x y) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substVarCommAux2 x u₁ y u₂ p with eq (rem x y) (rem x y)
substVarCommAux2 x u₁ y u₂ refl | .same = refl


substVarCommAux1 : ∀ {Γ σ τ} -> (x : Var Γ σ) -> (u₁ : Tm (Γ - x) σ) -> (y : Var (Γ - x) τ) -> (u₂ : Tm ((Γ - x) - y) τ) -> eq (wkv x y) (wkv (wkv x y) (rem x y)) ≡ diff (wkv x y) (rem x y) -> ! conExc x y >₁ hsubst.subst u₁ y u₂ ≡ hsubst.subst (substVar (wkv (wkv x y) (rem x y)) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substVarCommAux1 x u₁ y u₂ p with eq (wkv x y) (wkv (wkv x y) (rem x y))
substVarCommAux1 x u₁ y u₂ refl | .(diff (wkv x y) (rem x y)) = substVarCommAux2 x u₁ y u₂ (substSame3 (rem x y))


substVarCommAux4 : ∀ {Γ σ τ} -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) σ) -> (u₂ : Tm ((Γ - x) - y) σ) -> eq (wkv x y) (wkv x y) ≡ same -> ! conExc x y >₁ u₂ ≡ hsubst.subst (substVar (wkv x y) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substVarCommAux4 x u₁ y u₂ p with eq (wkv x y) (wkv x y)
substVarCommAux4 x u₁ y u₂ refl | .same = sym (weakSubst (rem x y) (! conExc x y >₁ u₂) (! conExc x y >₁ hsubst.subst u₁ y u₂))


substVarCommAux6 : ∀ {Γ σ τ ρ} -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> (v : Var ((Γ - x) - y) σ) -> eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ diff (rem x y) (! conExc x y >₀ v) -> ! conExc x y >₁ var v ≡ substVar (wkv (rem x y) (! conExc x y >₀ v)) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substVarCommAux6 x u₁ y u₂ v p with  eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v))
substVarCommAux6 x u₁ y u₂ v refl | .(diff (rem x y) (! conExc x y >₀ v)) = !var (conExc x y) v


substVarCommAux5 : ∀ {Γ σ τ ρ} -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> (v : Var ((Γ - x) - y) σ) -> eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ≡ diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) -> ! conExc x y >₁ var v ≡ hsubst.subst (substVar (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substVarCommAux5 x u₁ y u₂ v p with eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)))
substVarCommAux5 x u₁ y u₂ v refl | .(diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) = substVarCommAux6 x u₁ y u₂ v
                                                                                                (substDiff3 (rem x y) (! conExc x y >₀ v))


substVarCommAux3 : ∀ {Γ σ τ ρ} -> (x : Var Γ τ) -> (v : Var (Γ - x) σ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> ! conExc x y >₁ (substVar v y u₂) ≡ hsubst.subst (substVar (wkv x v) (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substVarCommAux3 x v u₁ y u₂ with eq y v
substVarCommAux3 x y u₁ .y u₂ | same = substVarCommAux4 x u₁ y u₂ (substSame3 (wkv x y))
substVarCommAux3 x .(wkv y v) u₁ .y u₂ | diff y v = begin
  _ ≡⟨ substVarCommAux5 x u₁ y u₂ v (substDiff3 (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ⟩
  _ ≡⟨ cong (λ z → hsubst.subst (substVar z (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)) (wkvExc x y v) ⟩
  _ ∎


substVarComm : ∀ {Γ σ τ ρ} -> (v : Var Γ σ) -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> ! conExc x y >₁ hsubst.subst (substVar v x u₁) y u₂ ≡ hsubst.subst (substVar v (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substVarComm v x u₁ y u₂ with eq x v
substVarComm x .x u₁ y u₂ | same = begin
  _ ≡⟨ substVarCommAux1 x u₁ y u₂ (substDiff3 (wkv x y) (rem x y)) ⟩
  _ ≡⟨ cong (λ z → hsubst.subst (substVar z (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)) (wkRem x y) ⟩
  _ ∎
substVarComm .(wkv x v) .x u₁ y u₂ | diff x v = substVarCommAux3 x v u₁ y u₂


substComm : ∀ {σ Γ τ ρ} -> (t : Tm Γ σ) -> (x : Var Γ τ) -> (u₁ : Tm (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Tm ((Γ - x) - y) ρ) -> ! conExc x y >₁ hsubst.subst (hsubst.subst t x u₁) y u₂ ≡ hsubst.subst (hsubst.subst t (wkv x y) (wkTm (rem x y) (! conExc x y >₁ u₂))) (rem x y) (! conExc x y >₁ hsubst.subst u₁ y u₂)
substComm (var v) x u₁ y u₂ = substVarComm v x u₁ y u₂
substComm {σ ⇒ _} (Λ t) x u₁ y u₂ = begin
  _ ≡⟨ !Λ (conExc x y) (hsubst.subst (hsubst.subst t (vs x) (wkTm vz u₁)) (vs y) (wkTm vz u₂)) ⟩
  _ ≡⟨ cong Λ (substComm t (vs x) (wkTm vz u₁) (vs y) (wkTm vz u₂)) ⟩
  _ ≡⟨ cong (λ u → Λ (hsubst.subst (hsubst.subst t (vs (wkv x y)) (wkTm (vs (rem x y)) u)) (vs (rem x y)) (! cong (λ Θ → Θ , σ) (conExc x y) >₁ hsubst.subst (wkTm vz u₁) (vs y) (wkTm vz u₂)))) (!wkTm (conExc x y) u₂) ⟩
  _ ≡⟨ cong (λ u → Λ (hsubst.subst (hsubst.subst t (vs (wkv x y)) u) (vs (rem x y)) (! cong (λ Θ → Θ , σ) (conExc x y) >₁ hsubst.subst (wkTm vz u₁) (vs y) (wkTm vz u₂)))) (wkTmExc vz (rem x y) (! conExc x y >₁ u₂)) ⟩
  _ ≡⟨ cong (λ u → Λ (hsubst.subst (hsubst.subst t (vs (wkv x y)) (wkTm vz (wkTm (rem x y) (! conExc x y >₁ u₂)))) (vs (rem x y)) u)) (!≡₁ (cong (λ Θ → Θ , σ) (conExc x y)) (sym (wkTmSubstExc vz u₁ y u₂))) ⟩
  _ ≡⟨ cong (λ u → Λ (hsubst.subst (hsubst.subst t (vs (wkv x y)) (wkTm vz (wkTm (rem x y) (! conExc x y >₁ u₂)))) (vs (rem x y)) u)) (!wkTm (conExc x y) (hsubst.subst u₁ y u₂)) ⟩
  _ ∎
substComm (app t₁ t₂) x u₁ y u₂ = begin
  _ ≡⟨ !app (conExc x y) (hsubst.subst (hsubst.subst t₁ x u₁) y u₂) (hsubst.subst (hsubst.subst t₂ x u₁) y u₂) ⟩
  _ ≡⟨ cong₂ app (substComm t₁ x u₁ y u₂) (substComm t₂ x u₁ y u₂) ⟩
  _ ∎


-- -- Weakening and substituting

-- mutual

--   weakSubstNfAux : ∀ {Γ σ τ} -> (x : Var Γ τ) -> (v : Var (Γ - x) σ) -> (us : Sp (Γ - x) σ ○) -> (t : Nf (Γ - x) τ) -> eq x (wkv x v) ≡ diff x v -> ((ne (wkv x v , wkSp x us)) [ x := t ]) ≡ ne (v , us)
--   weakSubstNfAux x v us t p with eq x (wkv x v)
--   weakSubstNfAux x v us t refl | .(diff x v) = cong (λ ts → ne (v , ts)) (weakSubstSp x us t)


--   weakSubstNf : ∀ {Γ σ τ} -> (x : Var Γ τ) -> (u : Nf (Γ - x) σ) -> (t : Nf (Γ - x) τ) -> (wkNf x u) [ x := t ] ≡ u
--   weakSubstNf = {!!}
--   -- weakSubstNf x (λn u) t = cong λn (weakSubstNf (vs x) u (wkNf vz t))
--   -- weakSubstNf x (ne (v , us)) t = weakSubstNfAux x v us t (substDiff3 x v)


--   weakSubstSp : ∀ {Γ σ τ ρ} -> (x : Var Γ τ) -> (us : Sp (Γ - x) σ ρ) -> (t : Nf (Γ - x) τ) -> (wkSp x us) < x := t > ≡ us
--   weakSubstSp _ ε _ = refl
--   weakSubstSp x (u , us) t = cong₂ (λ n ts → (n , ts)) (weakSubstNf x u t) (weakSubstSp x us t)

--------------------------------------------------------------------------------
-- This module implements non trivial commutation lemmas between the          --
-- different functions that define hereditary substitutions.                  --
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

module lemmas4 where


open import hsubst
open import lemmas1
open import lemmas2
open import lemmas3

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning


mutual

  -- •[•:=•] and napp commute

  substNfNapp : ∀ {Γ σ τ ρ} -> (t₁ : Nf Γ (σ ⇒ τ)) -> (t₂ : Nf Γ σ) -> (x : Var Γ ρ) -> (u : Nf (Γ - x) ρ) -> (napp t₁ t₂) [ x := u ] ≡ napp (t₁ [ x := u ]) (t₂ [ x := u ])
  substNfNapp (λn t₁) t₂ x u = substNfComm t₁ vz t₂ x u


  -- •[•:=•] and ◇ commute

  substNfAppNf : ∀ {Γ σ τ ρ} -> (t : Nf Γ σ) -> (ts : Sp Γ σ τ) -> (x : Var Γ ρ) -> (u : Nf (Γ - x) ρ) -> (t ◇ ts) [ x := u ] ≡ (t [ x := u ]) ◇ (ts < x := u >)
  substNfAppNf t ε x u = refl
  substNfAppNf t (t' , ts) x u = begin
    _ ≡⟨ substNfAppNf (napp t t') ts x u ⟩
    _ ≡⟨ cong (λ u' → u' ◇ (ts < x := u >)) (substNfNapp t t' x u) ⟩
    _ ∎


  substNfCommAux2 : ∀ {Γ σ τ} -> (ts : Sp Γ σ ○) -> (x : Var Γ σ) -> (u₁ : Nf (Γ - x) σ) -> (y : Var (Γ - x) τ) -> (u₂ : Nf ((Γ - x) - y) τ) -> eq (rem x y) (rem x y) ≡ same -> ! conExc x y >₂ ((u₁ ◇ (ts < x := u₁ >)) [ y := u₂ ]) ≡ (ne (rem x y , ts < (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) >)) [ (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) ]
  substNfCommAux2 ts x u₁ y u₂ p with eq (rem x y) (rem x y)
  substNfCommAux2 ts x u₁ y u₂ refl | .same = begin
    _ ≡⟨ !≡₂ (conExc x y) (substNfAppNf u₁ (ts < x := u₁ >) y u₂) ⟩
    _ ≡⟨ !appNf (conExc x y) (u₁ [ y := u₂ ]) ((ts < x := u₁ >) < y := u₂ >) ⟩
    _ ≡⟨ cong (λ u → (! conExc x y >₂ (u₁ [ y := u₂ ])) ◇ u) (substSpComm ts x u₁ y u₂) ⟩
    _ ∎


  substNfCommAux1 : ∀ {Γ σ τ} -> (ts : Sp Γ σ ○) -> (x : Var Γ σ) -> (u₁ : Nf (Γ - x) σ) -> (y : Var (Γ - x) τ) -> (u₂ : Nf ((Γ - x) - y) τ) -> eq (wkv x y) (wkv (wkv x y) (rem x y)) ≡ diff (wkv x y) (rem x y) -> ! conExc x y >₂ ((u₁ ◇ (ts < x := u₁ >)) [ y := u₂ ]) ≡ ((ne (wkv (wkv x y) (rem x y) , ts)) [ (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) ]) [ (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) ]
  substNfCommAux1 ts x u₁ y u₂ p with eq (wkv x y) (wkv (wkv x y) (rem x y))
  substNfCommAux1 ts x u₁ y u₂ refl | .(diff (wkv x y) (rem x y)) = substNfCommAux2 ts x u₁ y u₂ (substSame3 (rem x y))


  substNfCommAux4 : ∀ {Γ σ τ} -> (ts : Sp Γ σ ○) -> (x : Var Γ τ) -> (u₁ : Nf (Γ - x) τ) -> (y : Var (Γ - x) σ) -> (u₂ : Nf ((Γ - x) - y) σ) -> eq (wkv x y) (wkv x y) ≡ same -> ! conExc x y >₂ (u₂ ◇ ((ts < x := u₁ >) < y := u₂ >)) ≡ ((ne (wkv x y , ts)) [ (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) ]) [ (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) ]
  substNfCommAux4 ts x u₁ y u₂ p with eq (wkv x y) (wkv x y)
  substNfCommAux4 ts x u₁ y u₂ refl | .same = begin
    _ ≡⟨ !appNf (conExc x y) u₂ ((ts < x := u₁ >) < y := u₂ >) ⟩
    _ ≡⟨ cong (λ u → (! conExc x y >₂ u₂) ◇ u) (substSpComm ts x u₁ y u₂) ⟩
    _ ≡⟨ cong (λ u → u ◇ ((ts < wkv x y := wkNf (rem x y) (! conExc x y >₂ u₂) >) < rem x y := ! conExc x y >₂ (u₁ [ y := u₂ ]) >)) (sym (weakSubstNf (rem x y) (! conExc x y >₂ u₂) (! conExc x y >₂ (u₁ [ y := u₂ ])))) ⟩
    _ ≡⟨ sym (substNfAppNf (wkNf (rem x y) (! conExc x y >₂ u₂)) (ts < (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) >) (rem x y) (! conExc x y >₂ (u₁ [ y := u₂ ]))) ⟩
    _ ∎


  substNfCommAux6 : ∀ {Γ σ τ ρ} -> (ts : Sp Γ σ ○) -> (x : Var Γ τ) -> (u₁ : Nf (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Nf ((Γ - x) - y) ρ) -> (v : Var ((Γ - x) - y) σ) -> eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ diff (rem x y) (! conExc x y >₀ v) -> ! conExc x y >₂ ne (v , (ts < x := u₁ >) < y := u₂ >) ≡ (ne (wkv (rem x y) (! conExc x y >₀ v) , ts < (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) >)) [ (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) ]
  substNfCommAux6 ts x u₁ y u₂ v p with eq (rem x y) (wkv (rem x y) (! conExc x y >₀ v))
  substNfCommAux6 ts x u₁ y u₂ v refl | .(diff (rem x y) (! conExc x y >₀ v)) = begin
    _ ≡⟨ !ne (conExc x y) v ((ts < x := u₁ >) < y := u₂ >) ⟩
    _ ≡⟨ cong (λ u → ne ((! conExc x y >₀ v) , u)) (substSpComm ts x u₁ y u₂) ⟩
    _ ∎


  substNfCommAux5 : ∀ {Γ σ τ ρ} -> (ts : Sp Γ σ ○) -> (x : Var Γ τ) -> (u₁ : Nf (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Nf ((Γ - x) - y) ρ) -> (v : Var ((Γ - x) - y) σ) -> eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ≡ diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) -> ! conExc x y >₂ ne (v , (ts < x := u₁ >) < y := u₂ >) ≡ ((ne (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) , ts)) [ (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) ]) [ (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) ]
  substNfCommAux5 ts x u₁ y u₂ v p with eq (wkv x y) (wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)))
  substNfCommAux5 ts x u₁ y u₂ v refl | .(diff (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) = substNfCommAux6 ts x u₁ y u₂ v
                                                                                                    (substDiff3 (rem x y) (! conExc x y >₀ v))


  substNfCommAux3 : ∀ {Γ σ τ ρ} -> (ts : Sp Γ σ ○) -> (x : Var Γ τ) -> (u₁ : Nf (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Nf ((Γ - x) - y) ρ) -> (v : Var (Γ - x) σ) -> ! conExc x y >₂ ((ne (v , ts < x := u₁ >)) [ y := u₂ ]) ≡ ((ne (wkv x v , ts)) [ (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) ]) [ (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) ]
  substNfCommAux3 ts x u₁ y u₂ v with eq y v
  substNfCommAux3 ts x u₁ .y u₂ y | same = substNfCommAux4 ts x u₁ y u₂ (substSame3 (wkv x y))
  substNfCommAux3 ts x u₁ .y u₂ .(wkv y v) | diff y v = begin
    _ ≡⟨ substNfCommAux5 ts x u₁ y u₂ v (substDiff3 (wkv x y) (wkv (rem x y) (! conExc x y >₀ v))) ⟩
    _ ≡⟨ cong (λ z → (ne (z , ts) [ wkv x y := wkNf (rem x y) (! conExc x y >₂ u₂) ]) [ rem x y := ! conExc x y >₂ (u₁ [ y := u₂ ]) ]) (wkvExc x y v) ⟩
    _ ∎


  substNfComm : ∀ {σ Γ τ ρ} -> (t : Nf Γ σ) -> (x : Var Γ τ) -> (u₁ : Nf (Γ - x) τ) -> (y : Var (Γ - x) ρ) -> (u₂ : Nf ((Γ - x) - y) ρ) -> ! conExc x y >₂ ((t [ x := u₁ ]) [ y := u₂ ]) ≡ (t [ (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) ]) [ (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) ]
  substNfComm {σ ⇒ _} (λn t) x u₁ y u₂ = begin
    _ ≡⟨ !λn (conExc x y) ((t [ (vs x) := (wkNf vz u₁) ]) [ (vs y) := (wkNf vz u₂) ]) ⟩
    _ ≡⟨ cong λn (substNfComm t (vs x) (wkNf vz u₁) (vs y) (wkNf vz u₂)) ⟩
    _ ≡⟨ cong (λ u → λn ((t [ vs (wkv x y) := wkNf (vs (rem x y)) u ]) [ vs (rem x y) := ! cong (λ Θ → Θ , σ) (conExc x y) >₂ (wkNf vz u₁ [ vs y := wkNf vz u₂ ]) ])) (!wkNf (conExc x y) u₂) ⟩
    _ ≡⟨ cong (λ u → λn ((t [ vs (wkv x y) := u ]) [ vs (rem x y) := ! cong (λ Θ → Θ , σ) (conExc x y) >₂ (wkNf vz u₁ [ vs y := wkNf vz u₂ ]) ])) (wkNfExc vz (rem x y) (! conExc x y >₂ u₂)) ⟩
    _ ≡⟨ cong (λ u → λn ((t [ vs (wkv x y) := wkNf vz (wkNf (rem x y) (! conExc x y >₂ u₂)) ]) [ vs (rem x y) := u ])) (!≡₂ (cong (λ Θ → Θ , σ) (conExc x y)) (sym (wkNfSubstNfExc vz u₁ y u₂))) ⟩
    _ ≡⟨ cong (λ u → λn ((t [ vs (wkv x y) := wkNf vz (wkNf (rem x y) (! conExc x y >₂ u₂)) ]) [ vs (rem x y) := u ])) (!wkNf (conExc x y) (u₁ [ y := u₂ ])) ⟩
    _ ∎
  substNfComm (ne (v , ts)) x u₁ y u₂ with eq x v
  substNfComm (ne (x , ts)) .x u₁ y u₂ | same = begin
    _ ≡⟨ substNfCommAux1 ts x u₁ y u₂ (substDiff3 (wkv x y) (rem x y)) ⟩
    _ ≡⟨ cong (λ z → (ne (z , ts) [ wkv x y := wkNf (rem x y) (! conExc x y >₂ u₂) ]) [ rem x y := ! conExc x y >₂ (u₁ [ y := u₂ ]) ]) (wkRem x y) ⟩
    _ ∎
  substNfComm (ne (.(wkv x v) , ts)) .x u₁ y u₂ | diff x v = substNfCommAux3 ts x u₁ y u₂ v


  substSpComm : ∀ {Γ σ τ ρ} -> (ts : Sp Γ ρ ○) -> (x : Var Γ σ) -> (u₁ : Nf (Γ - x) σ) -> (y : Var (Γ - x) τ) -> (u₂ : Nf ((Γ - x) - y) τ) -> ! conExc x y >₃ (ts < x := u₁ >) < y := u₂ > ≡ (ts < (wkv x y) := (wkNf (rem x y) (! conExc x y >₂ u₂)) >) < (rem x y) := (! conExc x y >₂ (u₁ [ y := u₂ ])) >
  substSpComm ε x u₁ y u₂ = !ε (conExc x y)
  substSpComm (t , ts) x u₁ y u₂ = begin
    _ ≡⟨ !, (conExc x y) ((t [ x := u₁ ]) [ y := u₂ ]) ((ts < x := u₁ >) < y := u₂ >) ⟩
    _ ≡⟨ cong₂ (λ u us → u , us) (substNfComm t x u₁ y u₂) (substSpComm ts x u₁ y u₂) ⟩
    _ ∎

--------------------------------------------------------------------------------
-- This module implements hereditary substitutions for the simply-typed       --
-- λ-calculus.                                                                --
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


module hsubst where


-- Simple types

data Ty : Set where
  ○ : Ty
  _⇒_ : Ty → Ty → Ty


-- De Bruijn contexts

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con


-- De Bruijn indices (the set of variables)

data Var : Con → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ , σ) σ
  vs : ∀ {τ Γ σ} → Var Γ σ → Var (Γ , τ) σ


-- Removing a variable from a context

_-_ : {σ : Ty} → (Γ : Con) → Var Γ σ → Con
ε       - ()
(Γ , σ) - vz     = Γ
(Γ , τ) - (vs x) = (Γ - x) , τ


-- Conversely, adding a variable to a context (weakening)

wkv : ∀ {Γ σ τ} → (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)


-- The equality between variables: the predicate...

data EqV {Γ : Con} : {σ τ : Ty} → Var Γ σ → Var Γ τ → Set where
  same : ∀ {σ} → {x : Var Γ σ} → EqV {Γ} {σ} {σ} x x
  diff : ∀ {σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → EqV {Γ} {σ} {τ} x (wkv x y)


-- ... and the function that decides it

eq : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var Γ τ) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)


-- The set of normal forms

mutual

  data Nf : Con → Ty → Set where
    λn   : ∀ {Γ σ τ} → Nf (Γ , σ) τ → Nf Γ (σ ⇒ τ)
    ne   : ∀ {Γ σ} → Ne Γ σ → Nf Γ σ

  data Ne : Con → Ty → Set where
    _,_  : ∀ {Γ σ τ} → Var Γ σ → Sp Γ σ τ → Ne Γ τ

  data Sp : Con → Ty → Ty → Set where
    ε : ∀ {σ Γ} → Sp Γ σ σ
    _,_ : ∀ {Γ σ τ ρ} → Nf Γ τ → Sp Γ σ ρ → Sp Γ (τ ⇒ σ) ρ


-- Weakening of normal forms

mutual

  wkNf : ∀ {σ Γ τ} → (x : Var Γ σ) → Nf (Γ - x) τ → Nf Γ τ
  wkNf x (λn t)        = λn (wkNf (vs x) t)
  wkNf x (ne (y , us)) = ne (wkv x y , wkSp x us)

  wkSp :  ∀ {σ Γ τ ρ} → (x : Var Γ σ) → Sp (Γ - x) τ ρ → Sp Γ τ ρ
  wkSp x ε        = ε
  wkSp x (u , us) = (wkNf x u) , (wkSp x us)


-- Add a normal form at the end of a spine

appSp : ∀ {Γ σ τ ρ} → Sp Γ ρ (σ ⇒ τ) → Nf Γ σ → Sp Γ ρ τ
appSp ε u = (u , ε)
appSp (t , ts) u = ( t , appSp ts u)


-- η-expansion of normal forms

mutual

  nvar : ∀ {σ Γ} → Var Γ σ → Nf Γ σ
  nvar x = ne2nf (x , ε)

  ne2nf : ∀ {σ Γ} → Ne Γ σ → Nf Γ σ
  ne2nf = ne


-- Hereditary substitutions: substitute a variable by a normal form and
-- normalize the result

mutual

  napp : ∀ {τ σ Γ} → Nf Γ (σ ⇒ τ) → Nf Γ σ → Nf Γ τ
  napp (λn t) u = t [ vz := u ]
  napp (ne (f , xs)) u = ne (f , appSp xs u)

  _[_:=_] : ∀ {σ Γ τ} → (Nf Γ τ) → (x : Var Γ σ) → Nf (Γ - x) σ → Nf (Γ - x) τ
  (λn t) [ x := u ] = λn (t [ (vs x) := (wkNf vz u) ])
  (ne (y , ts))          [ x := u ] with eq x y
  (ne (x , ts))          [ .x := u ] | same      = u ◇ (ts < x := u >)
  (ne (.(wkv x y'), ts)) [ .x := u ] | diff x y' = ne (y' , (ts < x := u >))

  _<_:=_> : ∀ {Γ σ τ ρ} → Sp Γ τ ρ → (x : Var Γ σ) → Nf (Γ - x) σ → Sp (Γ - x) τ ρ
  ε < x := u > = ε
  (t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)


  -- apply a normal form to a spine

  _◇_ : ∀ {τ Γ σ} → Nf Γ σ → Sp Γ σ τ → Nf Γ τ
  t ◇ (u , us) = (napp t u) ◇ us
  t ◇ ε        = t


-- The set of terms

data Tm : Con → Ty → Set where
  var : ∀ {Γ σ} → Var Γ σ → Tm Γ σ
  Λ   : ∀ {Γ σ τ} → Tm (Γ , σ) τ → Tm Γ (σ ⇒ τ)
  app : ∀ {Γ σ τ} → Tm Γ (σ ⇒ τ) → Tm Γ σ → Tm Γ τ


-- The terms normalizer

nf : ∀ {Γ σ} → Tm Γ σ → Nf Γ σ
nf (var x)   = nvar x
nf (Λ t)     = λn (nf t)
nf (app t u) = napp (nf t) (nf u)


-- Embedding normal forms into terms
-- Normal forms are not defined as a subset of terms, but can be seen as
-- such

mutual

  -- Embedding of normal forms

  ⌈_⌉ : ∀ {Γ σ} → Nf Γ σ → Tm Γ σ
  ⌈ λn n ⌉ = Λ ⌈ n ⌉
  ⌈ ne n ⌉ = embNe n

  -- Embedding of ne

  embNe : ∀ {Γ σ} → Ne Γ σ → Tm Γ σ
  embNe (v , s) = embSp s (var v)

  -- Embedding of sp
  -- We have to use an accumulator

  embSp : ∀ {Γ σ τ} → Sp Γ σ τ → Tm Γ σ → Tm Γ τ
  embSp ε acc = acc
  embSp (n , s) acc = embSp s (app acc ⌈ n ⌉)


-- Weakening a term

wkTm : ∀ {σ Γ τ} → (x : Var Γ σ) → Tm (Γ - x) τ → Tm Γ τ
wkTm x (var v) = var (wkv x v)
wkTm x (Λ t) = Λ (wkTm (vs x) t)
wkTm x (app t₁ t₂) = app (wkTm x t₁) (wkTm x t₂)


-- Substitutions for variables and terms

substVar : ∀ {σ Γ τ} → Var Γ τ → (x : Var Γ σ) → Tm (Γ - x) σ → Tm (Γ - x) τ
substVar v x u with eq x v
substVar v .v u | same = u
substVar .(wkv v x) .v u | diff v x = var x


subst : ∀ {σ Γ τ} → Tm Γ τ → (x : Var Γ σ) → Tm (Γ - x) σ → Tm (Γ - x) τ
subst (var v) x u = substVar v x u
subst (Λ t) x u = Λ (subst t (vs x) (wkTm vz u))
subst (app t₁ t₂) x u = app (subst t₁ x u) (subst t₂ x u)

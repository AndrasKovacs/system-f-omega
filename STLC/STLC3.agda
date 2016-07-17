
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Ty : Set where
  ○   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε : Con
  _,_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀ {Γ σ} → Var (Γ , σ) σ
  vs : ∀ {τ Γ σ} → Var Γ σ → Var (Γ , τ) σ

_-_ : {σ : Ty} → (Γ : Con) → Var Γ σ → Con
ε       - ()
(Γ , σ) - vz     = Γ
(Γ , τ) - (vs x) = (Γ - x) , τ

wkv : ∀ {Γ σ τ} → (x : Var Γ σ) → Var (Γ - x) τ → Var Γ τ
wkv vz     y      = vs y
wkv (vs x) vz     = vz
wkv (vs x) (vs y) = vs (wkv x y)

data EqV {Γ : Con} : {σ τ : Ty} → Var Γ σ → Var Γ τ → Set where
  same : ∀ {σ} → {x : Var Γ σ} → EqV {Γ} {σ} {σ} x x
  diff : ∀ {σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → EqV {Γ} {σ} {τ} x (wkv x y)

eq : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var Γ τ) → EqV x y
eq vz      vz     = same
eq vz      (vs x) = diff vz x
eq (vs x)  vz     = diff (vs x) vz
eq (vs x)  (vs y) with eq x y
eq (vs x)  (vs .x)         | same       = same
eq (vs .x) (vs .(wkv x y)) | (diff x y) = diff (vs x) (vs y)

mutual
  data Nf : Con → Ty → Set where
    λn   : ∀ {Γ σ τ} → Nf (Γ , σ) τ → Nf Γ (σ ⇒ τ)
    ne   : ∀ {Γ} → Ne Γ ○ → Nf Γ ○

  data Ne : Con → Ty → Set where
    _,_  : ∀ {Γ σ τ} → Var Γ σ → Sp Γ σ τ → Ne Γ τ

  data Sp : Con → Ty → Ty → Set where
    ε : ∀ {σ Γ} → Sp Γ σ σ
    _,_ : ∀ {Γ σ τ ρ} → Nf Γ τ → Sp Γ σ ρ → Sp Γ (τ ⇒ σ) ρ

mutual

  wkNf : ∀ {σ Γ τ} → (x : Var Γ σ) → Nf (Γ - x) τ → Nf Γ τ
  wkNf x (λn t)        = λn (wkNf (vs x) t)
  wkNf x (ne (y , us)) = ne (wkv x y , wkSp x us)

  wkSp :  ∀ {σ Γ τ ρ} → (x : Var Γ σ) → Sp (Γ - x) τ ρ → Sp Γ τ ρ
  wkSp x ε        = ε
  wkSp x (u , us) = (wkNf x u) , (wkSp x us)

appSp : ∀ {Γ σ τ ρ} → Sp Γ ρ (σ ⇒ τ) → Nf Γ σ → Sp Γ ρ τ
appSp ε u = (u , ε)
appSp (t , ts) u = ( t , appSp ts u)

mutual
  nvar : ∀ {σ Γ} → Var Γ σ → Nf Γ σ
  nvar x = ne2nf (x , ε)

  ne2nf : ∀ {σ Γ} → Ne Γ σ → Nf Γ σ
  ne2nf {○}     xns      = ne xns
  ne2nf {σ ⇒ τ} (x , ns) = λn (ne2nf (vs x , appSp (wkSp vz ns) (nvar vz)))

mutual
  napp : ∀ {τ σ Γ} → Nf Γ (σ ⇒ τ) → Nf Γ σ → Nf Γ τ
  napp (λn t) u = t [ vz := u ]

  _[_:=_] : ∀ {σ Γ τ} → (Nf Γ τ) → (x : Var Γ σ) → Nf (Γ - x) σ → Nf (Γ - x) τ
  (λn t) [ x := u ] = λn (t [ (vs x) := (wkNf vz u) ])
  (ne (y , ts))          [ x := u ] with eq x y
  (ne (x , ts))          [ .x := u ] | same      = u ◇ (ts < x := u >)
  (ne (.(wkv x y'), ts)) [ .x := u ] | diff x y' = ne (y' , (ts < x := u >))

  _<_:=_> : ∀ {Γ σ τ ρ} → (Sp Γ τ ρ) → (x : Var Γ σ) → Nf (Γ - x) σ → Sp (Γ - x) τ ρ
  ε        < x := u > = ε
  (t , ts) < x := u > = (t [ x := u ]) , (ts < x := u >)

  _◇_ : ∀ {τ Γ σ} → Nf Γ σ → Sp Γ σ τ → Nf Γ τ
  t ◇ (u , us) = (napp t u) ◇ us
  t ◇ ε        = t

--------------------------------------------------------------------------------

substSame2 : ∀ {Γ σ τ} → (x : Var Γ σ) → eq x x ≡ same → eq (vs {τ} x) (vs x) ≡ same
substSame2 x p with eq x x
substSame2 x refl | .same = refl

substSame3 : ∀ {Γ σ} → (x : Var Γ σ) → eq x x ≡ same
substSame3 vz = refl
substSame3 (vs x) = substSame2 x (substSame3 x)


substDiff2 : ∀ {Γ σ τ ρ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y → eq (vs {ρ} x) (vs (wkv x y)) ≡ diff (vs x) (vs y)
substDiff2 x y p with eq x (wkv x y)
substDiff2 x y refl | .(diff x y) = refl


substDiff3 : ∀ {Γ σ τ} → (x : Var Γ σ) → (y : Var (Γ - x) τ) → eq x (wkv x y) ≡ diff x y
substDiff3 vz y = refl
substDiff3 (vs x) vz = refl
substDiff3 (vs x) (vs y) = substDiff2 x y (substDiff3 x y)

!_>₀_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Var Γ σ → Var Δ σ
! refl >₀ v = v

!vz : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → ! cong (_, σ) p >₀ vz ≡ vz
!vz refl = refl

!vs : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (x : Var Γ τ) → ! cong (_, σ) p >₀ (vs x) ≡ vs (! p >₀ x)
!vs refl _ = refl

!_>₂_ : ∀ {Γ Δ σ} → Γ ≡ Δ → Nf Γ σ → Nf Δ σ
! refl >₂ u = u

!_>₃_ : ∀ {Γ Δ σ τ} → Γ ≡ Δ → Sp Γ σ τ → Sp Δ σ τ
! refl >₃ us = us

!λn : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Nf (Γ , σ) τ) → ! p >₂ λn u ≡ λn (! cong (_, σ) p >₂ u)
!λn refl _ = refl

!ne : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → (x : Var Γ σ) → (ts : Sp Γ σ ○) → ! p >₂ ne (x , ts) ≡ ne ((! p >₀ x) , (! p >₃ ts))
!ne refl _ _ = refl

!wkNf : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Nf Γ τ) → ! cong (λ Θ → Θ , σ) p >₂ wkNf vz u ≡ wkNf vz (! p >₂ u)
!wkNf refl _ = refl

!appNf : ∀ {Γ Δ σ τ} → (p : Γ ≡ Δ) → (u : Nf Γ σ) → (ts : Sp Γ σ τ) → ! p >₂ (u ◇ ts) ≡ (! p >₂ u) ◇ (! p >₃ ts)
!appNf refl _ _ = refl

!≡₂ : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → {t₁ t₂ : Nf Γ σ} → t₁ ≡ t₂ → ! p >₂ t₁ ≡ ! p >₂ t₂
!≡₂ _ refl = refl

!ε : ∀ {Γ Δ σ} → (p : Γ ≡ Δ) → ! p >₃ ε {σ} ≡ ε
!ε refl = refl

!, : ∀ {Γ Δ σ τ ρ} → (p : Γ ≡ Δ) → (t : Nf Γ σ) → (ts : Sp Γ τ ρ) → (! p >₃ (t , ts)) ≡ ((! p >₂ t) , (! p >₃ ts))
!, refl _ _ = refl

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


wkvExc :
  ∀ {ρ Γ σ τ}(x : Var Γ σ)(y : Var (Γ - x) τ) (v : Var ((Γ - x) - y) ρ)
  → wkv (wkv x y) (wkv (rem x y) (! conExc x y >₀ v)) ≡ wkv x (wkv y v)
wkvExc vz _ _ = refl
wkvExc (vs x) vz _ = refl
wkvExc (vs x) (vs y) vz =  cong (λ v → wkv (vs (wkv x y)) (wkv (vs (rem x y)) v)) (!vz (conExc x y))
wkvExc (vs x) (vs y) (vs v) = begin
  _ ≡⟨ cong (λ z → wkv (vs (wkv x y)) (wkv (vs (rem x y)) z)) (!vs (conExc x y) v) ⟩
  _ ≡⟨ cong vs (wkvExc x y v) ⟩
  _ ∎


mutual

  wkNfExc :
    ∀ {Γ σ τ ρ}(x : Var Γ σ)(y : Var (Γ - x) τ)(t : Nf ((Γ - x) - y) ρ)
    → wkNf (wkv x y) (wkNf (rem x y) (! conExc x y >₂ t)) ≡ wkNf x (wkNf y t)
  wkNfExc x y (λn t) = begin
    _ ≡⟨ cong (λ u → wkNf (wkv x y) (wkNf (rem x y) u)) (!λn (conExc x y) t) ⟩
    _ ≡⟨ cong λn (wkNfExc (vs x) (vs y) t) ⟩
    _ ∎
  wkNfExc x y (ne (v , ts)) = begin
    _ ≡⟨ cong (λ t → wkNf (wkv x y) (wkNf (rem x y) t)) (!ne (conExc x y) v ts) ⟩
    _ ≡⟨ cong₂ (λ z us → ne (z , us)) (wkvExc x y v) (wkSpExc x y ts) ⟩
    _ ∎


  wkSpExc :
    ∀ {Γ σ τ ρ α}(x : Var Γ σ)(y : Var (Γ - x) τ)(ts : Sp ((Γ - x) - y) ρ α)
    → wkSp (wkv x y) (wkSp (rem x y) (! conExc x y >₃ ts)) ≡ wkSp x (wkSp y ts)
  wkSpExc x y ε = cong (λ ts → wkSp (wkv x y) (wkSp (rem x y) ts)) (!ε (conExc x y))
  wkSpExc x y (t , ts) = begin
    _ ≡⟨ cong (λ us → wkSp (wkv x y) (wkSp (rem x y) us)) (!, (conExc x y) t ts) ⟩
    _ ≡⟨ cong₂ (λ u us → u , us) (wkNfExc x y t) (wkSpExc x y ts) ⟩
    _ ∎

mutual

  nappWkNf :
    ∀ {Γ σ τ ρ}(x : Var Γ σ)(t₁ : Nf (Γ - x) (τ ⇒ ρ))(t₂ : Nf (Γ - x) τ)
    → wkNf x (napp t₁ t₂) ≡ napp (wkNf x t₁) (wkNf x t₂)
  nappWkNf x (λn t) u = wkNfSubstNfExc (vs x) t vz u

  appNfWkNfSp :
    ∀ {Γ σ τ ρ}(x : Var Γ σ)(u : Nf (Γ - x) τ)(ts : Sp (Γ - x) τ ρ)
    → (wkNf x u) ◇ (wkSp x ts) ≡ wkNf x (u ◇ ts)
  appNfWkNfSp x u ε = refl
  appNfWkNfSp x u (t , ts) = begin
    _ ≡⟨ cong (λ n → n ◇ wkSp x ts) (sym (nappWkNf x u t)) ⟩
    _ ≡⟨ appNfWkNfSp x (napp u t) ts ⟩
    _ ∎
    
  wkNfSubstNfExcAux1 :
    ∀ {Γ σ τ}(y : Var Γ σ)(ts : Sp (Γ - y) τ ○)(x : Var (Γ - y) τ)(u : Nf ((Γ - y) - x) τ)
    → eq (wkv y x) (wkv y x) ≡ same
    → wkNf (rem y x) (! conExc y x >₂ (u ◇ (ts < x := u >)))
    ≡ (ne (wkv y x , wkSp y ts)) [ (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) ]
  wkNfSubstNfExcAux1 y ts x u p with eq (wkv y x) (wkv y x)
  wkNfSubstNfExcAux1 y ts x u refl | .same = begin
    _ ≡⟨ cong (wkNf (rem y x)) (!appNf (conExc y x) u (ts < x := u >)) ⟩
    _ ≡⟨ sym (appNfWkNfSp (rem y x) (! conExc y x >₂ u) (! conExc y x >₃ (ts < x := u >))) ⟩
    _ ≡⟨ cong (λ n → wkNf (rem y x) (! conExc y x >₂ u) ◇ n) (wkSpSubstSpExc y ts x u) ⟩
    _ ∎

  wkNfSubstNfExcAux2 :
    ∀ {Γ σ τ ρ}(y : Var Γ σ)(ts : Sp (Γ - y) τ ○) (x : Var (Γ - y) ρ)(u : Nf ((Γ - y) - x) ρ)(v : Var ((Γ - y) - x) τ)
    
    → eq (wkv y x) (wkv (wkv y x) (wkv (rem y x) (! conExc y x >₀ v)))
    ≡ diff (wkv y x) (wkv (rem y x) (! conExc y x >₀ v))
    
    → wkNf (rem y x) (! conExc y x >₂ ne (v , (ts < x := u >)))
    ≡ (ne (wkv (wkv y x) (wkv (rem y x) (! conExc y x >₀ v)) , wkSp y ts)) [ (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) ]
  wkNfSubstNfExcAux2 y ts x u v p with eq (wkv y x) (wkv (wkv y x) (wkv (rem y x) (! conExc y x >₀ v)))
  wkNfSubstNfExcAux2 y ts x u v refl | .(diff (wkv y x) (wkv (rem y x) (! conExc y x >₀ v))) = begin
    _ ≡⟨ cong (wkNf (rem y x)) (!ne (conExc y x) v (ts < x := u >)) ⟩
    _ ≡⟨ cong (λ us → ne (wkv (rem y x) (! conExc y x >₀ v) , us)) (wkSpSubstSpExc y ts x u) ⟩
    _ ∎

  wkNfSubstNfExc :
    ∀ {Γ σ τ ρ}(y : Var Γ σ)(t : Nf (Γ - y) τ) (x : Var (Γ - y) ρ)(u : Nf ((Γ - y) - x) ρ)
    → wkNf (rem y x) (! conExc y x >₂ (t [ x := u ]))
    ≡ (wkNf y t) [ (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) ]
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

  wkSpSubstSpExc :
    ∀ {Γ σ τ ρ α}(y : Var Γ σ)(ts : Sp (Γ - y) τ ρ)(x : Var (Γ - y) α)(u : Nf ((Γ - y) - x) α)
    → wkSp (rem y x) (! conExc y x >₃ (ts < x := u >))
    ≡ (wkSp y ts) < (wkv y x) := (wkNf (rem y x) (! conExc y x >₂ u)) >
  wkSpSubstSpExc y ε x u = cong (wkSp (rem y x)) (!ε (conExc y x))
  wkSpSubstSpExc y (t , ts) x u = begin
    _ ≡⟨ cong (wkSp (rem y x)) (!, (conExc y x) (t [ x := u ]) (ts < x := u >)) ⟩
    _ ≡⟨ cong₂ (λ n us → n , us) (wkNfSubstNfExc y t x u) (wkSpSubstSpExc y ts x u) ⟩
    _ ∎

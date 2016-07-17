
open import Data.Sum renaming (map to smap)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (map to pmap)
open import Function
open import Data.Empty

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con
infixl 4 _▷_

data Ix : Con → Set where
  iz  : ∀ {Γ} → Ix Γ
  is_ : ∀ {A Γ} → Ix Γ → Ix (Γ ▷ A)

data _∈_ A : Con → Set where
  vz  : ∀ {Γ} → A ∈ (Γ ▷ A)
  vs_ : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▷ B)

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  ƛ_  : ∀ {A B} → Tm (Γ ▷ A) B → Tm Γ (A ⇒ B)
  _∙_ : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
infixl 8 _∙_

mutual
  data Nf Γ : Ty → Set where
    ƛ_ : ∀ {A B} → Nf (Γ ▷ A) B → Nf Γ (A ⇒ B)
    ne  : Ne Γ ⋆ → Nf Γ ⋆

  data Ne Γ : Ty → Set where
    _,_ : ∀ {A B} → A ∈ Γ → Sp Γ A B → Ne Γ B

  data Sp Γ : Ty → Ty → Set where
    ε   : ∀ {A} → Sp Γ A A
    _∷_ : ∀ {A B C} → Nf Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  infixr 5 _∷_

data _⊆_ : Con → Con → Set where
  stop : ε ⊆ ε
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ ▷ A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ ▷ A) ⊆ (Δ ▷ A)

idᵒ : ∀ {Γ} → Γ ⊆ Γ
idᵒ {ε}     = stop
idᵒ {Γ ▷ _} = keep idᵒ

top : ∀ {A Γ} → Γ ⊆ (Γ ▷ A)
top = add idᵒ

drop : ∀ {Γ} → Ix Γ → Con
drop {Γ}     iz     = Γ
drop {Γ ▷ _} (is i) = drop i

drop-⊆ : ∀ {Γ} i → drop {Γ} i ⊆ Γ
drop-⊆ iz     = idᵒ
drop-⊆ (is i) = add (drop-⊆ i)

ins : ∀ {Γ} → Ix Γ → Ty → Con
ins {Γ}     iz     A = Γ ▷ A
ins {Γ ▷ B} (is i) A = ins i A ▷ B

ins-⊆ : ∀ {Γ} i A → Γ ⊆ ins {Γ} i A
ins-⊆ iz     A = top
ins-⊆ (is i) A = keep (ins-⊆ i A)

snocSp : ∀ {Γ A B C} → Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
snocSp ε       t = t ∷ ε
snocSp (x ∷ s) t = x ∷ snocSp s t

ren-Ix : ∀ {Γ Δ} → Γ ⊆ Δ → Ix Γ → Ix Δ
ren-Ix stop     i      = i
ren-Ix (add o)  i      = is ren-Ix o i
ren-Ix (keep o) iz     = iz
ren-Ix (keep o) (is i) = is ren-Ix o i

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ stop ()
ren-∈ (add o)  v      = vs ren-∈ o v
ren-∈ (keep o) vz     = vz
ren-∈ (keep o) (vs v) = vs ren-∈ o v

∈-Eq : Con → Ty → Ty → Set
∈-Eq Γ A B = (A ≡ B) ⊎ (B ∈ Γ)

∈-eq : ∀ {Γ A B} i → B ∈ (ins {Γ} i A) → ∈-Eq Γ A B
∈-eq iz     vz     = inj₁ refl
∈-eq iz     (vs v) = inj₂ v
∈-eq (is i) vz     = inj₂ vz
∈-eq (is i) (vs v) = smap id vs_ (∈-eq i v)

ren-∈-Eq : ∀ {Γ Δ A B} → Γ ⊆ Δ → ∈-Eq Γ A B → ∈-Eq Δ A B
ren-∈-Eq o = smap id (ren-∈ o)

mutual
 ren : ∀ {Γ Δ A} → Γ ⊆ Δ → Nf Γ A → Nf Δ A
 ren o (ƛ A)         = ƛ ren (keep o) A 
 ren o (ne (v , sp)) = ne (ren-∈ o v , renSp o sp)

 renSp : ∀ {Γ Δ A B} → Γ ⊆ Δ → Sp Γ A B → Sp Δ A B
 renSp o ε        = ε
 renSp o (A ∷ sp) = ren o A ∷ renSp o sp

mutual
  η : ∀ {Γ A} → A ∈ Γ → Nf Γ A
  η v = η-Ne (v , ε)

  η-Ne : ∀ {A Γ} → Ne Γ A → Nf Γ A
  η-Ne {⋆}     n        = ne n
  η-Ne {A ⇒ B} (v , sp) = ƛ η-Ne ((vs v) , snocSp (renSp top sp) (η vz))

mutual
  sub : ∀ {Γ A B} (i : Ix Γ) → Nf Γ A → Nf (ins i A) B → Nf Γ B
  sub i t' (ƛ t) = ƛ (sub (is i) (ren top t') t)
  sub i t' (ne (v , sp)) with ∈-eq i v | subSp i t' sp
  ... | inj₁ refl | sp' = appSp t' sp'
  ... | inj₂ v'   | sp' = ne (v' , sp')

  subSp : ∀ {Γ A B C} (i : Ix Γ) → Nf Γ A → Sp (ins i A) B C → Sp Γ B C
  subSp i t' ε        = ε
  subSp i t' (t ∷ sp) = sub i t' t ∷ subSp i t' sp

  appSp : ∀ {Γ A B} → Nf Γ A → Sp Γ A B → Nf Γ B
  appSp t      ε       = t
  appSp (ƛ f) (x ∷ sp) = appSp (sub iz x f) sp

-- Categorical stuff for _⊆_ 
--------------------------------------------------------------------------------

_∘ᵒ_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
stop   ∘ᵒ ι      = ι
add  κ ∘ᵒ ι      = add  (κ ∘ᵒ ι)
keep κ ∘ᵒ add  ι = add  (κ ∘ᵒ ι)
keep κ ∘ᵒ keep ι = keep (κ ∘ᵒ ι)

idᵒ-∘ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → idᵒ ∘ᵒ ι ≡ ι
idᵒ-∘  stop    = refl
idᵒ-∘ (add  ι) = cong add (idᵒ-∘ ι)
idᵒ-∘ (keep ι) = cong keep (idᵒ-∘ ι)

∘-idᵒ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → ι ∘ᵒ idᵒ ≡ ι
∘-idᵒ  stop    = refl
∘-idᵒ (add  ι) = cong add (∘-idᵒ ι)
∘-idᵒ (keep ι) = cong keep (∘-idᵒ ι)

ren-∈-id : ∀ {Γ A} (v : A ∈ Γ) → ren-∈ idᵒ v ≡ v
ren-∈-id  vz    = refl
ren-∈-id (vs v) = cong vs_ (ren-∈-id v)

-- ren-∈-Eq-∘ : 

ren-∈-∘ :
  ∀ {Γ Δ Ξ A} (o : Δ ⊆ Ξ) (o' : Γ ⊆ Δ) (v : A ∈ Γ)
  → ren-∈ o (ren-∈ o' v) ≡ ren-∈ (o ∘ᵒ o') v
ren-∈-∘  stop     stop     ()
ren-∈-∘ (add  o)  o'        v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) (add  o')  v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) (keep o')  vz    = refl
ren-∈-∘ (keep o) (keep o') (vs v) = cong vs_ (ren-∈-∘ o o' v)

mutual
  ren-∘ : ∀ {Γ Δ Ξ A}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(t : Nf Γ A) → ren o (ren o' t) ≡ ren (o ∘ᵒ o') t
  ren-∘ o o' (ƛ  t)        = cong ƛ_ (ren-∘ (keep o) (keep o') t)
  ren-∘ o o' (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-∘ o o' v) (renSp-∘ o o' sp)

  renSp-∘ :
    ∀ {Γ Δ Ξ A B}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(sp : Sp Γ A B)
    → renSp o (renSp o' sp) ≡ renSp (o ∘ᵒ o') sp
  renSp-∘ o o' ε        = refl
  renSp-∘ o o' (t ∷ sp) = cong₂ _∷_ (ren-∘ o o' t) (renSp-∘ o o' sp)

--------------------------------------------------------------------------------

inj₂-inj : ∀ {A B : Set}{x y : B} → ((A ⊎ B) ∋ inj₂ x) ≡ inj₂ y → x ≡ y
inj₂-inj refl = refl

⊎-conflict : ∀ {A B : Set}{x : A}{y : B} → ((A ⊎ B) ∋ inj₁ x) ≢ inj₂ y
⊎-conflict ()

∈-eq-ins :
  ∀ {Γ A} B i (v : A ∈ Γ) → ∈-eq i (ren-∈ (ins-⊆ i B) v) ≡ inj₂ v
∈-eq-ins A iz     vz     = refl
∈-eq-ins A iz     (vs v) = cong (inj₂ ∘ vs_) (ren-∈-id v)
∈-eq-ins A (is i) vz     = refl
∈-eq-ins A (is i) (vs v) = cong (smap id vs_) (∈-eq-ins A i v)  

mutual
  sub-ren : ∀ {Γ A B} i (t' : Nf Γ B)(t : Nf Γ A) → sub i t' (ren (ins-⊆ i B) t) ≡ t
  sub-ren i t' (ƛ t) = cong ƛ_ (sub-ren (is i) (ren top t') t)
  sub-ren {B = B} i t' (ne (v , sp))
    with ∈-eq i (ren-∈ (ins-⊆ i B) v) | inspect (∈-eq i) (ren-∈ (ins-⊆ i B) v)
  ... | inj₂ v'   | [ eq ] =
   cong₂ (λ x y → ne (x , y))
     (inj₂-inj $ trans (sym eq) (∈-eq-ins B i v))
     (subSp-ren i t' sp)    
  ... | inj₁ refl | [ eq ]
    = ⊥-elim $ ⊎-conflict $ sym $ trans (sym $ ∈-eq-ins B i v) eq

  subSp-ren :
    ∀ {Γ A B C} i (t' : Nf Γ B)(sp : Sp Γ A C) → subSp i t' (renSp (ins-⊆ i B) sp) ≡ sp
  subSp-ren i t' ε        = refl
  subSp-ren i t' (x ∷ sp) = cong₂ _∷_ (sub-ren i t' x) (subSp-ren i t' sp)

--------------------------------------------------------------------------------
  
⊆-ins : ∀ {A Γ Δ} i → (o : Γ ⊆ Δ) → ins {Γ} i A ⊆ ins (ren-Ix o i) A
⊆-ins i      stop     = idᵒ
⊆-ins i      (add o)  = add (⊆-ins i o)
⊆-ins iz     (keep o) = keep (keep o)
⊆-ins (is i) (keep o) = keep (⊆-ins i o)

top-keep :
  ∀ {Γ Δ A B}(t : Nf Γ A)(o : Γ ⊆ Δ)
  → ren top (ren o t) ≡ ren (keep o) (ren (top {B}) t)
top-keep {B = B} t o rewrite
    ren-∘ (top{B}) o t
  | ren-∘ (keep o) (top {B}) t
  | idᵒ-∘ o
  | ∘-idᵒ o
  = refl

smap-∘ :
  ∀ {A A' A'' B B' B'' : Set}(f : A' → A'')(g : B' → B'')(h : A → A')(i : B → B') x
  → smap f g (smap h i x) ≡ smap (f ∘ h) (g ∘ i) x
smap-∘ f g h i (inj₁ x) = refl
smap-∘ f g h i (inj₂ y) = refl  

∈-eq-ins-comm :
  ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(i : Ix Γ)(v : A ∈ ins i B)
  → ∈-eq (ren-Ix o i) (ren-∈ (⊆-ins i o) v) ≡ ren-∈-Eq o (∈-eq i v)
∈-eq-ins-comm stop     iz vz     = refl
∈-eq-ins-comm (add o)  iz vz     = cong (smap id vs_) (∈-eq-ins-comm o iz vz)
∈-eq-ins-comm (keep o) iz vz     = refl
∈-eq-ins-comm stop     iz (vs v) = refl
∈-eq-ins-comm (add o)  iz (vs v) = cong (smap id vs_ ) (∈-eq-ins-comm o iz (vs v))
∈-eq-ins-comm (keep o) iz (vs v) = refl
∈-eq-ins-comm (add o)  (is i) vz = cong (smap id vs_) (∈-eq-ins-comm o (is i) vz)
∈-eq-ins-comm (keep o) (is i) vz = refl
∈-eq-ins-comm (add {A'} o)  (is i) (vs v) rewrite
    ∈-eq-ins-comm o (is i) (vs v)
  | smap-∘ id (vs_ {_}{A'}) id (ren-∈ o) (smap id vs_ (∈-eq i v))
  = refl
∈-eq-ins-comm (keep {A'} o) (is i) (vs v) rewrite
    ∈-eq-ins-comm o i v
  | smap-∘ id (vs_ {_}{A'}) id (ren-∈ o) (∈-eq i v)
  | smap-∘ id (ren-∈ (keep {A'} o)) id vs_ (∈-eq i v)
  = refl

⊆-ins-iz : ∀ {Γ Δ A} o → ⊆-ins {A}{Γ}{Δ} iz o ≡ {!!}
⊆-ins-iz o = {!!}

mutual
  sub-ren-comm :
    ∀ {Γ Δ A B}(i : Ix Γ)(o : Γ ⊆ Δ)(t' : Nf Γ A)(t : Nf (ins i A) B) → 
    ren o (sub i t' t) ≡ sub (ren-Ix o i) (ren o t') (ren (⊆-ins i o) t)
  sub-ren-comm i o t' (ƛ_ {A = A} t)
    rewrite top-keep {B = A} t' o = cong ƛ_ (sub-ren-comm (is i) (keep o) (ren top t') t)
  sub-ren-comm i o t' (ne (v , sp)) with
      ∈-eq (ren-Ix o i) (ren-∈ (⊆-ins i o) v)
    | ∈-eq-ins-comm o i v
    | ∈-eq i v
    | inspect (∈-eq i) v
  ... | inj₁ refl | _ | inj₁ refl | [ _  ] rewrite sym $ subSp-ren-comm i o t' sp
    = appSp-ren-comm o t' (subSp i t' sp)
  ... | inj₂ v'   | p | inj₂ _    | [ eq ] rewrite eq
    = cong₂ (λ x y → ne (x , y)) (inj₂-inj (sym p)) (subSp-ren-comm i o t' sp)
  ... | inj₂ v'   | p | inj₁ _ | [ eq ] rewrite eq = ⊥-elim $ ⊎-conflict $ sym p
  ... | inj₁ refl | p | inj₂ _ | [ eq ] rewrite eq = ⊥-elim $ ⊎-conflict p

  subSp-ren-comm :
    ∀ {Γ Δ A B C}(i : Ix Γ)(o : Γ ⊆ Δ)(t' : Nf Γ A)(sp : Sp (ins i A) B C)
    → renSp o (subSp i t' sp) ≡ subSp (ren-Ix o i) (ren o t') (renSp (⊆-ins i o) sp)
  subSp-ren-comm i o t' ε        = refl
  subSp-ren-comm i o t' (t ∷ sp) = cong₂ _∷_ (sub-ren-comm i o t' t) (subSp-ren-comm i o t' sp)

  appSp-ren-comm :
    ∀ {Γ Δ A B} (o : Γ ⊆ Δ) (t : Nf Γ A)(sp : Sp Γ A B) 
    → ren o (appSp t sp) ≡ appSp (ren o t) (renSp o sp)
  appSp-ren-comm o t ε            = refl
  appSp-ren-comm o (ƛ t) (x ∷ sp) = trans (appSp-ren-comm o (sub iz x t) sp)
    (cong (λ x₁ → appSp x₁ (renSp o sp)) (trans (sub-ren-comm iz o x t) {!⊆-ins iz o!}))    



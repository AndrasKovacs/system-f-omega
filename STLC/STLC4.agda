
open import Data.Sum renaming (map to smap)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (map to pmap)
open import Function
open import Data.Empty
open import Data.Unit

data Ty : Set where
  ⋆   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ε   : Con
  _▷_ : Con → Ty → Con
infixl 4 _▷_

data Ix : Con → Set where
  iz : ∀ Γ → Ix Γ
  is : ∀ A {Γ} → Ix Γ → Ix (Γ ▷ A)

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
  keep : ∀ A {Γ Δ} → Γ ⊆ Δ → (Γ ▷ A) ⊆ (Δ ▷ A)

idᵒ : ∀ {Γ} → Γ ⊆ Γ
idᵒ {ε}     = stop
idᵒ {Γ ▷ _} = keep _ idᵒ

top : ∀ A {Γ} → Γ ⊆ (Γ ▷ A)
top _ = add idᵒ

ins : ∀ Γ → Ix Γ → Ty → Con
ins Γ       (iz _)   A = Γ ▷ A
ins (Γ ▷ B) (is _ i) A = ins Γ i A ▷ B

snocSp : ∀ {Γ A B C} → Sp Γ A (B ⇒ C) → Nf Γ B → Sp Γ A C
snocSp ε       t = t ∷ ε
snocSp (x ∷ s) t = x ∷ snocSp s t

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ stop ()
ren-∈ (add o)  v      = vs ren-∈ o v
ren-∈ (keep _ o) vz     = vz
ren-∈ (keep _ o) (vs v) = vs ren-∈ o v

∈-Eq : Con → Ty → Ty → Set
∈-Eq Γ A B = (A ≡ B) ⊎ (B ∈ Γ)

∈-eq : ∀ {Γ A B} i → B ∈ (ins Γ i A) → ∈-Eq Γ A B
∈-eq (iz _)     vz     = inj₁ refl
∈-eq (iz _)     (vs v) = inj₂ v
∈-eq (is _ i) vz     = inj₂ vz
∈-eq (is _ i) (vs v) = smap id vs_ (∈-eq i v)

ren-∈-Eq : ∀ {Γ Δ A B} → Γ ⊆ Δ → ∈-Eq Γ A B → ∈-Eq Δ A B
ren-∈-Eq o = smap id (ren-∈ o)

mutual
 ren : ∀ {Γ Δ A} → Γ ⊆ Δ → Nf Γ A → Nf Δ A
 ren o (ƛ A)         = ƛ ren (keep _ o) A 
 ren o (ne (v , sp)) = ne (ren-∈ o v , renSp o sp)

 renSp : ∀ {Γ Δ A B} → Γ ⊆ Δ → Sp Γ A B → Sp Δ A B
 renSp o ε        = ε
 renSp o (A ∷ sp) = ren o A ∷ renSp o sp

mutual
  η : ∀ {Γ A} → A ∈ Γ → Nf Γ A
  η v = η-Ne (v , ε)

  η-Ne : ∀ {A Γ} → Ne Γ A → Nf Γ A
  η-Ne {⋆}     n        = ne n
  η-Ne {A ⇒ B} (v , sp) = ƛ η-Ne ((vs v) , snocSp (renSp (top _) sp) (η vz))

mutual
  sub : ∀ {Γ A B} (i : Ix Γ) → Nf Γ A → Nf (ins Γ i A) B → Nf Γ B
  sub i t' (ƛ t) = ƛ (sub (is _ i) (ren (top _) t') t)
  sub i t' (ne (v , sp)) with ∈-eq i v | subSp i t' sp
  ... | inj₁ refl | sp' = appSp t' sp'
  ... | inj₂ v'   | sp' = ne (v' , sp')

  subSp : ∀ {Γ A B C} (i : Ix Γ) → Nf Γ A → Sp (ins Γ i A) B C → Sp Γ B C
  subSp i t' ε        = ε
  subSp i t' (t ∷ sp) = sub i t' t ∷ subSp i t' sp

  appNf : ∀ {Γ A B} → Nf Γ (A ⇒ B) → Nf Γ A → Nf Γ B
  appNf (ƛ f) x = sub (iz _) x f

  appSp : ∀ {Γ A B} → Nf Γ A → Sp Γ A B → Nf Γ B
  appSp t  ε       = t
  appSp f (x ∷ sp) = appSp (appNf f x) sp

-- Categorical stuff for _⊆_ 
--------------------------------------------------------------------------------

_∘ᵒ_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
stop   ∘ᵒ ι      = ι
add  κ ∘ᵒ ι      = add  (κ ∘ᵒ ι)
keep _ κ ∘ᵒ add  ι = add  (κ ∘ᵒ ι)
keep _ κ ∘ᵒ keep _ ι = keep _ (κ ∘ᵒ ι)

idᵒ-∘ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → idᵒ ∘ᵒ ι ≡ ι
idᵒ-∘  stop    = refl
idᵒ-∘ (add  ι) = cong add (idᵒ-∘ ι)
idᵒ-∘ (keep _ ι) = cong (keep _) (idᵒ-∘ ι)

∘-idᵒ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → ι ∘ᵒ idᵒ ≡ ι
∘-idᵒ  stop    = refl
∘-idᵒ (add  ι) = cong add (∘-idᵒ ι)
∘-idᵒ (keep _ ι) = cong (keep _) (∘-idᵒ ι)

ren-∈-id : ∀ {Γ A} (v : A ∈ Γ) → ren-∈ idᵒ v ≡ v
ren-∈-id  vz    = refl
ren-∈-id (vs v) = cong vs_ (ren-∈-id v)

ren-∈-∘ :
  ∀ {Γ Δ Ξ A} (o : Δ ⊆ Ξ) (o' : Γ ⊆ Δ) (v : A ∈ Γ)
  → ren-∈ o (ren-∈ o' v) ≡ ren-∈ (o ∘ᵒ o') v
ren-∈-∘  stop     stop     ()
ren-∈-∘ (add  o)  o'        v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep _ o) (add  o')  v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep _ o) (keep _ o')  vz    = refl
ren-∈-∘ (keep _ o) (keep _ o') (vs v) = cong vs_ (ren-∈-∘ o o' v)

mutual
  ren-∘ : ∀ {Γ Δ Ξ A}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(t : Nf Γ A) → ren o (ren o' t) ≡ ren (o ∘ᵒ o') t
  ren-∘ o o' (ƛ  t)        = cong ƛ_ (ren-∘ (keep _ o) (keep _ o') t)
  ren-∘ o o' (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-∘ o o' v) (renSp-∘ o o' sp)

  renSp-∘ :
    ∀ {Γ Δ Ξ A B}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(sp : Sp Γ A B)
    → renSp o (renSp o' sp) ≡ renSp (o ∘ᵒ o') sp
  renSp-∘ o o' ε        = refl
  renSp-∘ o o' (t ∷ sp) = cong₂ _∷_ (ren-∘ o o' t) (renSp-∘ o o' sp)

mutual
  ren-id : ∀ {Γ A} (t : Nf Γ A) → ren idᵒ t ≡ t
  ren-id (ƛ t)         = cong ƛ_ (ren-id t)
  ren-id (ne (v , sp)) =
    cong₂ (λ a b → ne (a , b)) (ren-∈-id v) (renSp-id sp)

  renSp-id : ∀ {Γ A B} (sp : Sp Γ A B) → renSp idᵒ sp ≡ sp
  renSp-id ε        = refl
  renSp-id (x ∷ sp) = cong₂ _∷_ (ren-id x) (renSp-id sp)

--------------------------------------------------------------------------------

Sub : ∀ {Γ Δ} → Ix Γ → Γ ⊆ Δ → Set
Sub (iz Γ)   o           = ⊤
Sub (is A i) (add o)     = ⊥
Sub (is A i) (keep .A o) = Sub i o

ren-Ix : ∀ {Γ Δ}(o : Γ ⊆ Δ)(i : Ix Γ) → Sub i o → Ix Δ
ren-Ix o          (iz Γ)    p = iz _
ren-Ix (add o)    (is A i) ()
ren-Ix (keep A o) (is .A i) p = is A (ren-Ix o i p)

⊆-ins : ∀ {A Γ Δ} (o : Γ ⊆ Δ) i p → ins Γ i A ⊆ ins Δ (ren-Ix o i p) A
⊆-ins o          (iz Γ)     p = keep _ o
⊆-ins (add o)    (is A i)  ()
⊆-ins (keep A o) (is .A i)  p = keep A (⊆-ins o i p)

mutual
  appNf-ren-comm : ∀ {Γ Δ A B}(o : Γ ⊆ Δ) (f : Nf Γ (A ⇒ B)) x → ren o (appNf f x) ≡ appNf (ren o f) (ren o x)
  appNf-ren-comm o (ƛ f) x = foo o (iz _) f x _  
  
  foo :
    ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(i : Ix Γ) (t : Nf (ins Γ i A) B)(t' : Nf Γ A)(p : Sub i o)
    → ren o (sub i t' t) ≡ sub (ren-Ix o i p) (ren o t') (ren (⊆-ins o i p) t) 
  foo o i (ƛ t)  t' p = cong ƛ_ {!foo (keep _ o) (is _ i) t (ren (top _) t') p!}
  foo o i (ne x) t' p = {!!}  
  
-- ren o (sub i x f) ≡ sub i ? (ren (keep o) f)



-- ren o (sub iz x f) ≡ sub iz (ren o x) (ren (keep o) f)

-- (ƛ ren (keep o) (sub (is iz) (ren top x) f)) ≡
--    (ƛ sub (is iz) (ren top (ren o x)) (ren (keep (keep o)) f))










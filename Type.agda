
module SystemFOmega.Type where

open import Data.Empty
open import Data.Product renaming (map to pmap)
open import Data.Sum renaming (map to smap)
open import Data.Unit
open import Function using (_$_; _∋_)
open import Relation.Binary.PropositionalEquality

import Function as F
import Relation.Binary.HeterogeneousEquality as H

data Kind : Set where
  ⋆   : Kind
  _⇒_ : Kind → Kind → Kind
infixr 2 _⇒_

data Con : Set where
  ε   : Con
  _▷_ : Con → Kind → Con
infixl 4 _▷_

data _∈_ A : Con → Set where
  vz  : ∀ {Γ} → A ∈ (Γ ▷ A)
  vs_ : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ ▷ B)

mutual
  data Ty Γ : Kind → Set where
    _⇒_ : Ty Γ ⋆ → Ty Γ ⋆ → Ty Γ ⋆
    ƛ_  : ∀ {A B} → Ty (Γ ▷ A) B → Ty Γ (A ⇒ B)
    ∀'_ : ∀ {A}   → Ty (Γ ▷ A) ⋆ → Ty Γ ⋆
    ne  : Ne Γ ⋆ → Ty Γ ⋆

  data Ne Γ : Kind → Set where
    _,_ : ∀ {A B} → A ∈ Γ → Sp Γ A B → Ne Γ B

  data Sp Γ : Kind → Kind → Set where
    ε   : ∀ {A} → Sp Γ A A
    _∷_ : ∀ {A B C} → Ty Γ A → Sp Γ B C → Sp Γ (A ⇒ B) C
  infixr 5 _∷_

data _⊆_ : Con → Con → Set where
  stop : ε ⊆ ε
  add  : ∀ {A Γ Δ} → Γ ⊆ Δ → Γ ⊆ (Δ ▷ A)
  keep : ∀ {A Γ Δ} → Γ ⊆ Δ → (Γ ▷ A) ⊆ (Δ ▷ A)

id : ∀ {Γ} → Γ ⊆ Γ
id {ε}     = stop
id {Γ ▷ _} = keep id

top : ∀ {A Γ} → Γ ⊆ (Γ ▷ A)
top = add id

ren-∈ : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Γ → A ∈ Δ
ren-∈ stop ()
ren-∈ (add o)  v      = vs ren-∈ o v
ren-∈ (keep o) vz     = vz
ren-∈ (keep o) (vs v) = vs ren-∈ o v

mutual
  ren : ∀ {Γ Δ A} → Γ ⊆ Δ → Ty Γ A → Ty Δ A
  ren o (A ⇒ B)       = ren o A ⇒ ren o B
  ren o (∀' t)        = ∀' ren (keep o) t
  ren o (ƛ t)         = ƛ (ren (keep o) t)
  ren o (ne (v , sp)) = ne ((ren-∈ o v) , renSp o sp)

  renSp : ∀ {Γ Δ A B} → Γ ⊆ Δ → Sp Γ A B → Sp Δ A B
  renSp o ε        = ε
  renSp o (x ∷ sp) = ren o x ∷ renSp o sp

drop : ∀ {Γ A} → A ∈ Γ → Con
drop {Γ ▷ _} vz     = Γ
drop {Γ ▷ _} (vs v) = drop v

subᶜ : ∀ {Γ A} → A ∈ Γ → Con
subᶜ {Γ ▷ _} vz     = Γ
subᶜ {Γ ▷ A} (vs v) = subᶜ v ▷ A

drop-sub-⊆ : ∀ {Γ A} (v : A ∈ Γ) → drop v ⊆ subᶜ v
drop-sub-⊆ vz     = id
drop-sub-⊆ (vs v) = add (drop-sub-⊆ v)

⊆-drop : ∀ {Γ Δ A}(v : A ∈ Γ)(o : Γ ⊆ Δ) → drop v ⊆ drop (ren-∈ o v)
⊆-drop  ()    stop
⊆-drop  v     (add o)  = ⊆-drop v o
⊆-drop  vz    (keep o) = o
⊆-drop  (vs v)(keep o) = ⊆-drop v o

⊆-subᶜ : ∀ {Γ Δ A}(v : A ∈ Γ)(o : Γ ⊆ Δ) → subᶜ v ⊆ subᶜ (ren-∈ o v)
⊆-subᶜ ()     stop
⊆-subᶜ v      (add o)  = add (⊆-subᶜ v o)
⊆-subᶜ vz     (keep o) = o
⊆-subᶜ (vs v) (keep o) = keep (⊆-subᶜ v o)

∈-eq : ∀ {Γ A B}(v : A ∈ Γ)(v' : B ∈ Γ) → (A ≡ B) ⊎ (B ∈ subᶜ v)
∈-eq vz     vz      = inj₁ refl
∈-eq vz     (vs v') = inj₂ v'
∈-eq (vs v) vz      = inj₂ vz
∈-eq (vs v) (vs v') = smap (λ z → z) vs_ (∈-eq v v')

mutual
  sub : ∀ {Γ A B} → (v : A ∈ Γ) → Ty (drop v) A → Ty Γ B → Ty (subᶜ v) B
  sub v t' (A ⇒ B) = sub v t' A ⇒ sub v t' B
  sub v t' (∀' t)  = ∀' sub (vs v) t' t
  sub v t' (ƛ t)   = ƛ  sub (vs v) t' t
  sub v t' (ne (v' , sp)) with ∈-eq v v' | subSp v t' sp
  ... | inj₁ refl | sp' = ren (drop-sub-⊆ v) t' ◇ sp'
  ... | inj₂ v''  | sp' = ne (v'' , sp')

  subSp : ∀ {Γ A B C} → (v : A ∈ Γ) → Ty (drop v) A → Sp Γ B C → Sp (subᶜ v) B C
  subSp v t' ε        = ε
  subSp v t' (t ∷ sp) = sub v t' t ∷ subSp v t' sp

  _◇_ : ∀ {Γ A B} → Ty Γ A → Sp Γ A B → Ty Γ B
  t     ◇ ε        = t
  (ƛ t) ◇ (x ∷ sp) = sub vz x t ◇ sp

inst : ∀ {Γ A B} → Ty Γ A → Ty (Γ ▷ A) B → Ty Γ B
inst = sub vz

snocSp : ∀ {Γ A B C} → Sp Γ A (B ⇒ C) → Ty Γ B → Sp Γ A C
snocSp ε       t = t ∷ ε
snocSp (x ∷ s) t = x ∷ snocSp s t

mutual
  η : ∀ {Γ A} → A ∈ Γ → Ty Γ A
  η v = η-Ne (v , ε)

  η-Ne : ∀ {A Γ} → Ne Γ A → Ty Γ A
  η-Ne {⋆}     n        = ne n
  η-Ne {A ⇒ B} (v , sp) = ƛ η-Ne ((vs v) , snocSp (renSp top sp) (η vz))

-- Categorical stuff for _⊆_
--------------------------------------------------------------------------------

_∘_ : ∀ {Γ Δ Ξ} → Δ ⊆ Ξ → Γ ⊆ Δ → Γ ⊆ Ξ
stop   ∘ ι      = ι
add  κ ∘ ι      = add  (κ ∘ ι)
keep κ ∘ add  ι = add  (κ ∘ ι)
keep κ ∘ keep ι = keep (κ ∘ ι)

id-∘ : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → id ∘ ι ≡ ι
id-∘  stop    = refl
id-∘ (add  ι) = cong add (id-∘ ι)
id-∘ (keep ι) = cong keep (id-∘ ι)

∘-id : ∀ {Γ Δ} → (ι : Γ ⊆ Δ) → ι ∘ id ≡ ι
∘-id  stop    = refl
∘-id (add  ι) = cong add (∘-id ι)
∘-id (keep ι) = cong keep (∘-id ι)

ren-∈-id : ∀ {Γ A} (v : A ∈ Γ) → ren-∈ id v ≡ v
ren-∈-id  vz    = refl
ren-∈-id (vs v) = cong vs_ (ren-∈-id v)

ren-∈-∘ :
  ∀ {Γ Δ Ξ A} (o : Δ ⊆ Ξ) (o' : Γ ⊆ Δ) (v : A ∈ Γ)
  → ren-∈ o (ren-∈ o' v) ≡ ren-∈ (o ∘ o') v
ren-∈-∘  stop     stop     ()
ren-∈-∘ (add  o)  o'        v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) (add  o')  v     = cong vs_ (ren-∈-∘ o o' v)
ren-∈-∘ (keep o) (keep o')  vz    = refl
ren-∈-∘ (keep o) (keep o') (vs v) = cong vs_ (ren-∈-∘ o o' v)

mutual
  ren-∘ : ∀ {Γ Δ Ξ A}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(t : Ty Γ A) → ren o (ren o' t) ≡ ren (o ∘ o') t
  ren-∘ o o' (A ⇒ B)       = cong₂ _⇒_ (ren-∘ o o' A) (ren-∘ o o' B)
  ren-∘ o o' (∀' A)        = cong ∀'_ (ren-∘ (keep o) (keep o') A)
  ren-∘ o o' (ƛ  t)        = cong ƛ_ (ren-∘ (keep o) (keep o') t)
  ren-∘ o o' (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-∘ o o' v) (renSp-∘ o o' sp)

  renSp-∘ :
    ∀ {Γ Δ Ξ A B}(o : Δ ⊆ Ξ)(o' : Γ ⊆ Δ)(sp : Sp Γ A B)
    → renSp o (renSp o' sp) ≡ renSp (o ∘ o') sp
  renSp-∘ o o' ε        = refl
  renSp-∘ o o' (t ∷ sp) = cong₂ _∷_ (ren-∘ o o' t) (renSp-∘ o o' sp)

mutual
  ren-id : ∀ {Γ A}(t : Ty Γ A) → ren id t ≡ t
  ren-id (A ⇒ B)       = cong₂ _⇒_ (ren-id A) (ren-id B)
  ren-id (ƛ t)         = cong ƛ_ (ren-id t)
  ren-id (∀' t)        = cong ∀'_ (ren-id t)
  ren-id (ne (v , sp)) = cong₂ (λ x y → ne (x , y)) (ren-∈-id v) (renSp-id sp)

  renSp-id : ∀ {Γ A B}(sp : Sp Γ A B) → renSp id sp ≡ sp
  renSp-id ε        = refl
  renSp-id (t ∷ sp) = cong₂ _∷_ (ren-id t) (renSp-id sp)


-- Properties
--------------------------------------------------------------------------------

Fresh : ∀ {Γ Δ A} → Γ ⊆ Δ → A ∈ Δ → Set
Fresh stop ()
Fresh (add o)  vz     = ⊤
Fresh (add o)  (vs v) = Fresh o v
Fresh (keep o) vz     = ⊥
Fresh (keep o) (vs v) = Fresh o v

Fresh-sub-⊆ : ∀ {Γ Δ A v} o → Fresh {Γ}{Δ}{A} o v → Γ ⊆ subᶜ v
Fresh-sub-⊆ {v = vz}   (add o)  f = o
Fresh-sub-⊆ {v = vz}   (keep o) ()
Fresh-sub-⊆ {v = vs v} (add o)  f = add (Fresh-sub-⊆ o f)
Fresh-sub-⊆ {v = vs v} (keep o) f = keep (Fresh-sub-⊆ o f)

fresh-∈-eq :
 ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(v : A ∈ Δ)(v' : B ∈ Γ)(f : Fresh o v)
 → ∈-eq v (ren-∈ o v') ≡ inj₂ (ren-∈ (Fresh-sub-⊆ o f) v')
fresh-∈-eq stop     ()     v' f
fresh-∈-eq (keep o) vz     v' ()
fresh-∈-eq (add o)  vz     v' f = refl
fresh-∈-eq (keep o) (vs v) vz f = refl
fresh-∈-eq (add o)  (vs v) v'      f rewrite fresh-∈-eq o v v' f = refl
fresh-∈-eq (keep o) (vs v) (vs v') f rewrite fresh-∈-eq o v v' f = refl

mutual
  fresh-sub :
    ∀ {Γ Δ A B} (o : Γ ⊆ Δ) (v : A ∈ Δ)(f : Fresh o v)(t' : Ty (drop v) A)(t : Ty Γ B)
    → sub v t' (ren o t) ≡ ren (Fresh-sub-⊆ o f) t
  fresh-sub o v f t' (A ⇒ B) rewrite fresh-sub o v f t' A | fresh-sub o v f t' B = refl
  fresh-sub o v f t' (ƛ t)  = cong ƛ_ (fresh-sub (keep o) (vs v) f t' t)
  fresh-sub o v f t' (∀' t) = cong ∀'_ (fresh-sub (keep o) (vs v) f t' t)
  fresh-sub o v f t' (ne (v' , sp)) with ∈-eq v (ren-∈ o v') | fresh-∈-eq o v v' f
  ... | inj₁ refl | ()
  ... | inj₂ _    | refl = cong (λ x → ne (_ , x)) (fresh-sub-Sp o v f t' sp)

  fresh-sub-Sp :
    ∀ {Γ Δ A B C} (o : Γ ⊆ Δ) (v : A ∈ Δ)(f : Fresh o v)(t' : Ty (drop v) A)(sp : Sp Γ B C)
    → subSp v t' (renSp o sp) ≡ renSp (Fresh-sub-⊆ o f) sp
  fresh-sub-Sp o v f t' ε        = refl
  fresh-sub-Sp o v f t' (x ∷ sp) = cong₂ _∷_ (fresh-sub o v f t' x) (fresh-sub-Sp o v f t' sp)

inst-top : ∀ {Γ A B} (t' : Ty Γ A)(t : Ty Γ B) → inst t' (ren top t) ≡ t
inst-top t' t = trans (fresh-sub top vz _ t' t) (ren-id t)

--------------------------------------------------------------------------------

top-add : ∀ {Γ Δ A B}(o : Γ ⊆ Δ)(t : Ty Γ A) → ren (top {B}) (ren o t) ≡ ren (add o) t
top-add {B = B} o t rewrite ren-∘ (top{B}) o t | id-∘ o = refl

top-keep :
  ∀ {Γ Δ A B}(t : Ty Γ A)(o : Γ ⊆ Δ) → ren top (ren o t) ≡ ren (keep o) (ren (top {B}) t)
top-keep {B = B} t o rewrite
  ren-∘ (top{B}) o t | ren-∘ (keep o) (top {B}) t | id-∘ o | ∘-id o = refl

--------------------------------------------------------------------------------

ren-sub-∈ :
  ∀ {Γ Δ A B}(o : Γ ⊆ Δ) (v : A ∈ Γ) (v' : B ∈ Γ)
  → ∈-eq (ren-∈ o v) (ren-∈ o v') ≡ smap F.id (ren-∈ (⊆-subᶜ v o)) (∈-eq v v')
ren-sub-∈ stop () v'
ren-sub-∈ (add o) v v' with ren-sub-∈ o v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ x | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ y | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep o) (vs v) (vs v') with ren-sub-∈ o v v' | ∈-eq v v' | inspect (∈-eq v) v'
... | rec | inj₁ x | [ eq ] rewrite rec | eq = refl
... | rec | inj₂ y | [ eq ] rewrite rec | eq = refl
ren-sub-∈ (keep o) vz    vz      = refl
ren-sub-∈ (keep o) vz    (vs v') = refl
ren-sub-∈ (keep o) (vs v) vz     = refl

ren-drop-sub' :
  ∀ {Γ Δ A}(o : Γ ⊆ Δ)(v : A ∈ Γ)
  → (⊆-subᶜ v o ∘ drop-sub-⊆ v) ≡ (drop-sub-⊆ (ren-∈ o v) ∘ ⊆-drop v o)
ren-drop-sub' stop ()
ren-drop-sub' (add o)  v      = cong add (ren-drop-sub' o v)
ren-drop-sub' (keep o) vz     = trans (∘-id o) (sym (id-∘ o))
ren-drop-sub' (keep o) (vs v) = cong add (ren-drop-sub' o v)

ren-drop-sub :
  ∀ {Γ Δ A}(o : Γ ⊆ Δ)(v : A ∈ Γ)(t : Ty (drop v) A)
  → ren (⊆-subᶜ v o) (ren (drop-sub-⊆ v) t) ≡ ren (drop-sub-⊆ (ren-∈ o v)) (ren (⊆-drop v o) t)
ren-drop-sub o v t rewrite
  ren-∘ (⊆-subᶜ v o) (drop-sub-⊆ v) t | ren-∘ (drop-sub-⊆ (ren-∈ o v)) (⊆-drop v o) t
  = cong (λ x → ren x t) (ren-drop-sub' o v)

mutual
  ren-sub :
    ∀ {Γ Δ A B} (v : A ∈ Γ) (o : Γ ⊆ Δ) t' (t : Ty Γ B)
    → ren (⊆-subᶜ v o) (sub v t' t) ≡ sub (ren-∈ o v) (ren (⊆-drop v o) t') (ren o t)
  ren-sub v o t' (A ⇒ B) rewrite ren-sub v o t' A | ren-sub v o t' B = refl
  ren-sub v o t' (ƛ t)  = cong ƛ_  (ren-sub (vs v) (keep o) t' t)
  ren-sub v o t' (∀' t) = cong ∀'_ (ren-sub (vs v) (keep o) t' t)
  ren-sub v o t' (ne (v' , sp))
    with ∈-eq (ren-∈ o v) (ren-∈ o v') | ∈-eq v v' | ren-sub-∈ o v v'
  ... | inj₁ refl | inj₁ _    | refl rewrite
    sym $ ren-sub-Sp v o t' sp | ren-sub-◇ (⊆-subᶜ v o) (ren (drop-sub-⊆ v) t') (subSp v t' sp)
    = cong (_◇ renSp (⊆-subᶜ v o) (subSp v t' sp)) (ren-drop-sub o v t')
  ... | inj₂ _    | inj₂ v''  | refl rewrite ren-sub-Sp v o t' sp = refl
  ... | inj₁ refl | inj₂ _    | ()
  ... | inj₂ _    | inj₁ refl | ()

  ren-sub-Sp :
    ∀ {Γ Δ A B C} (v : A ∈ Γ) (o : Γ ⊆ Δ) t' (sp : Sp Γ B C) →
    renSp (⊆-subᶜ v o) (subSp v t' sp) ≡ subSp (ren-∈ o v) (ren (⊆-drop v o) t') (renSp o sp)
  ren-sub-Sp v o t' ε        = refl
  ren-sub-Sp v o t' (x ∷ sp) = cong₂ _∷_ (ren-sub v o t' x) (ren-sub-Sp v o t' sp)

  ren-sub-◇ :
    ∀ {Γ Δ A B}(o : Γ ⊆ Δ) (t : Ty Γ A) (sp : Sp Γ A B) →
    ren o (t ◇ sp) ≡ ren o t ◇ renSp o sp
  ren-sub-◇ o t     ε        = refl
  ren-sub-◇ o (ƛ t) (x ∷ sp) rewrite
    ren-sub-◇ o (inst x t) sp | ren-sub vz (keep o) x t = refl

--------------------------------------------------------------------------------

ixcong :
  ∀ {I : Set}{A : I → Set}(B : ∀ {i} → A i → Set){i i'}{x : A i}{y : A i'}
  → i ≡ i'
  → (f : ∀ {i} (a : A i) → B a) → x H.≅ y → f x H.≅ f y
ixcong B refl f H.refl = H.refl

⊆-subᶜ-id : ∀ {Γ A} (v : A ∈ Γ) → ⊆-subᶜ v id H.≅ id {subᶜ v}
⊆-subᶜ-id {Γ ▷ A} vz     = H.refl
⊆-subᶜ-id {Γ ▷ A} (vs v) =
  ixcong (λ {x} _ → (subᶜ v ▷ A) ⊆ (subᶜ x ▷ A)) (ren-∈-id v) keep (⊆-subᶜ-id v)

⊆-drop-id : ∀ {Γ A}(v : A ∈ Γ) → ⊆-drop v id H.≅ id {drop v}
⊆-drop-id vz     = H.refl
⊆-drop-id (vs v) = ⊆-drop-id v

ren-top-sub :
  ∀ {Γ A B C}(v : A ∈ Γ) (t' : Ty (drop v) A) (t : Ty Γ B)
  → ren (top {C}) (sub v t' t) ≡ sub (vs v) t' (ren (top {C}) t)
ren-top-sub {Γ}{A}{B}{C} v t' t = H.≅-to-≡
  (H.trans
    (ixcong
      (λ {x} _ → Ty (subᶜ x ▷ C) B)
      (sym $ ren-∈-id v)
      (λ r → ren (add r) (sub v t' t))
      (H.sym (⊆-subᶜ-id v)))
    (H.trans
      (H.≡-to-≅ (ren-sub v top t' t))
      (H.trans
        (ixcong
          (λ {x} _ → Ty (subᶜ x ▷ C) B)
          (ren-∈-id v)
          (λ {x} r → sub (vs x) (ren r t') (ren top t))
          (⊆-drop-id v))
        (H.cong
          (λ x → sub (vs v) x (ren top t))
          (H.≡-to-≅ (ren-id t'))))))


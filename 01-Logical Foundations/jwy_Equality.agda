-- Equality: Equality and equational reasoning

-- We declare equality as follows:
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

-- It is straightforward to show symmetry:
sym : ∀ {A : Set} {x y : A}
  → x ≡ y
  -----
  → y ≡ x
sym refl = refl

-- Transitivity is equally straightforward:
trans : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  -----
  → x ≡ z
trans refl refl  =  refl

-- Equality satisfies congruence.
-- If two terms are equal,
-- they remain so after the same function is applied to both:
cong : ∀ {A B : Set} (f : A → B) {x y : A}
  → x ≡ y
  ---------
  → f x ≡ f y
cong f refl  =  refl

-- Congruence of functions with two arguments is similar:
cong₂ : ∀ {A B C : Set} (f : A → B → C) {u x : A} {v y : B}
  → u ≡ x
  → v ≡ y
  -------------
  → f u v ≡ f x y
cong₂ f refl refl  =  refl

-- Equality is also a congruence in the function position of an application.
-- If two functions are equal,
-- then applying them to the same term yields equal terms:
cong-app : ∀ {A B : Set} {f g : A → B}
  → f ≡ g
  ---------------------
  → ∀ (x : A) → f x ≡ g x
cong-app refl x = refl

-- Equality also satisfies substitution.
-- If two values are equal and a predicate holds of the first
-- then it also holds of the second:
subst : ∀ {A : Set} {x y : A} (P : A → Set)
  → x ≡ y
  ---------
  → P x → P y
subst P refl px = px

-- Chains of equations
module ≡-Reasoning {A : Set} where

  infix  1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  3 _∎

  begin_ : ∀ {x y : A}
    → x ≡ y
    -----
    → x ≡ y
  begin x≡y  =  x≡y

  _≡⟨⟩_ : ∀ (x : A) {y : A}
    → x ≡ y
    -----
    → x ≡ y
  x ≡⟨⟩ x≡y  =  x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A}
    → x ≡ y
    → y ≡ z
    -----
    → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

  _∎ : ∀ (x : A)
    -----
    → x ≡ x
  x ∎  =  refl

open ≡-Reasoning

-- a proof of transitivity as a chain of equations:
trans′ : ∀ {A : Set} {x y z : A}
  → x ≡ y
  → y ≡ z
  -----
  → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

-- Chains of equations, another example
-- We repeat the proof that addition is commutative.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero    + n  =  n
(suc m) + n  =  suc (m + n)

postulate
  +-identity : ∀ (m : ℕ) → m + zero ≡ m
  +-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identity m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

-- Exercise ≤-Reasoning (stretch)
-- The proof of monotonicity from Chapter Relations can be written in a more readable form
-- by using an analogue of our notation for ≡-Reasoning.
-- Define ≤-Reasoning analogously,
-- and use it to write out an alternative proof that addition is monotonic with regard to inequality.
-- Rewrite all of +-monoˡ-≤, +-monoʳ-≤, and +-mono-≤.

module ≤-Reasoning where

  data _≤_ : ℕ → ℕ → Set where

    z≤n : ∀ {n : ℕ}
      --------
      → zero ≤ n

    s≤s : ∀ {m n : ℕ}
      → m ≤ n
      -------------
      → suc m ≤ suc n
  infix 4 _≤_
  ≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
    -----
    → m ≤ p
  ≤-trans z≤n       _          =  z≤n
  ≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

  ≤-refl : ∀ {n : ℕ}
     -----
     → n ≤ n
  ≤-refl {zero} = z≤n
  ≤-refl {suc n} = s≤s ≤-refl

  infix  1 ≤begin_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix  3 _≤∎

  ≤begin_ : ∀ {x y : ℕ}
    → x ≤ y
    -----
    → x ≤ y
  ≤begin x≤y  =  x≤y

  _≤⟨⟩_ : ∀ (x : ℕ) {y : ℕ}
    → x ≤ y
    -----
    → x ≤ y
  x ≤⟨⟩ x≤y  =  x≤y

  _≤⟨_⟩_ : ∀ (x : ℕ) {y z : ℕ}
    → x ≤ y
    → y ≤ z
    -----
    → x ≤ z
  x ≤⟨ x≤y ⟩ y≤z  =  ≤-trans x≤y y≤z

  _≤∎ : ∀ (x : ℕ)
    -----
    → x ≤ x
  x ≤∎  =  ≤-refl

open ≤-Reasoning

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =
  ≤begin
    p ≤⟨ p≤q ⟩ q
  ≤∎
+-monoʳ-≤ (suc n) p q p≤q  =
  ≤begin
    suc n + p
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc n + q
  ≤∎
-- TODO



-- Rewriting
-- We repeat the earlier definition:
data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where

  odd-suc : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)


{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ (m n : ℕ)
  → even (m + n)
  ------------
  → even (n + m)
even-comm m n ev  rewrite +-comm n m  =  ev


-- Multiple rewrites
+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ zero    n  rewrite +-identity n             =  refl
+-comm′ (suc m) n  rewrite +-suc n m | +-comm′ m n  =  refl

even-comm′ : ∀ (m n : ℕ)
  → even (m + n)
  ------------
  → even (n + m)
even-comm′ m n ev with   m + n  | +-comm m n
...                  | .(n + m) | refl       = ev

even-comm″ : ∀ (m n : ℕ)
  → even (m + n)
  ------------
  → even (n + m)
even-comm″ m n  =  subst even (+-comm m n)


-- Leibniz equality
_≐_ : ∀ {A : Set} (x y : A) → Set₁
_≐_ {A} x y = ∀ (P : A → Set) → P x → P y

refl-≐ : ∀ {A : Set} {x : A}
  → x ≐ x
refl-≐ P Px =  Px

trans-≐ : ∀ {A : Set} {x y z : A}
  → x ≐ y
  → y ≐ z
  -----
  → x ≐ z
trans-≐ x≐y y≐z P Px  =  y≐z P (x≐y P Px)

sym-≐ : ∀ {A : Set} {x y : A}
  → x ≐ y
  -----
  → y ≐ x
sym-≐ {A} {x} {y} x≐y P  =  Qy
  where
    Q : A → Set
    Q z = P z → P x
    Qx : Q x
    Qx = refl-≐ P
    Qy : Q y
    Qy = x≐y Q Qx

≡-implies-≐ : ∀ {A : Set} {x y : A}
  → x ≡ y
  -----
  → x ≐ y
≡-implies-≐ x≡y P  =  subst P x≡y

-- Universe polymorphism
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : ∀ {ℓ : Level} {A : Set ℓ} {x y : A}
  → x ≡′ y
  ------
  → y ≡′ x
sym′ refl′ = refl′

_≐′_ : ∀ {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = ∀ (P : A → Set ℓ) → P x → P y

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)


-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

-- 定义小于等于关系
data _≤_ : ℕ → ℕ → Set where

  z≤n : ∀ {n : ℕ}
    --------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      -------------
    → suc m ≤ suc n

-- 隐式参数的例子
_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)


_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _

infix 4 _≤_

-- 反演性
inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
    -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    --------
  → m ≡ zero
inv-z≤n z≤n = refl


-- 练习 orderings（实践）
-- 给出一个不是偏序的预序的例子。
-- 给出一个不是全序的偏序的例子。

-- 自反性
≤-refl : ∀ {n : ℕ}
       -----
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl
-- ≤-refl {zero} = z≤n {zero}
-- ≤-refl {suc n} = s≤s {n} {n} (≤-refl {n}) 

-- 传递性
≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    -----
  → m ≤ p
≤-trans z≤n       _          =  z≤n
≤-trans (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans m≤n n≤p)

-- 反对称性
≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -----
  → m ≡ n
≤-antisym z≤n       z≤n        =  refl
≤-antisym (s≤s m≤n) (s≤s n≤m)  =  cong suc (≤-antisym m≤n n≤m)

-- 练习 ≤-antisym-cases（实践）
-- 上面的证明中省略了一个参数是 z≤n，另一个参数是 s≤s 的情况。
-- 为什么可以省略这种情况？
-- ≤-antisym z≤n s≤s = ?
-- because unification ended with a conflicting equation
-- suc n ≟ zero

-- 完全性
data Total (m n : ℕ) : Set where

  forward :
    m ≤ n
    ---------
    → Total m n

  flipped :
    n ≤ m
    ---------
    → Total m n

data Total′ : ℕ → ℕ → Set where

  forward′ : ∀ {m n : ℕ}
    → m ≤ n
    ----------
    → Total′ m n

  flipped′ : ∀ {m n : ℕ}
    → n ≤ m
    ----------
    → Total′ m n

-- 证明完全性，使用 with 语句
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero    n                         =  forward z≤n
≤-total (suc m) zero                      =  flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n  =  forward (s≤s m≤n)
...                        | flipped n≤m  =  flipped (s≤s n≤m)

-- 证明完全性，使用 where 语句
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
    helper : Total m n → Total (suc m) (suc n)
    helper (forward m≤n)  =  forward (s≤s m≤n)
    helper (flipped n≤m)  =  flipped (s≤s n≤m)

-- 模式匹配时参数的顺序
≤-total″ : ∀ (m n : ℕ) → Total m n
≤-total″ m       zero                      =  flipped z≤n
≤-total″ zero    (suc n)                   =  forward z≤n
≤-total″ (suc m) (suc n) with ≤-total″ m n
...                         | forward m≤n  =  forward (s≤s m≤n)
...                         | flipped n≤m  =  flipped (s≤s n≤m)

-- 对加法的单调性
+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  -------------
  → n + p ≤ n + q
+-monoʳ-≤ zero    p q p≤q  =  p≤q
+-monoʳ-≤ (suc n) p q p≤q  =  s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  -------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n  rewrite +-comm m p | +-comm n p  = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  -------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q  =  ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- 对乘法的单调性
*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
  -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero    p q p≤q  =  z≤n
*-monoʳ-≤ (suc n) p q p≤q  =  (+-mono-≤  p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q))

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
  -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n  rewrite *-comm m p | *-comm n p  = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
  -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q  =  ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- 定义严格不等关系
infix 4 _<_

data _<_ : ℕ → ℕ → Set where

  z<s : ∀ {n : ℕ}
    ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
    -------------
    → suc m < suc n

-- 练习 <-trans （推荐）
-- 证明严格不等是传递的。请直接证明。（后续的练习中我们将使用 < 和 ≤ 的关系。）

<-trans : (m n q : ℕ)
  → m < n
  → n < q
  ----------
  → m < q

<-trans zero         _  (suc q)         _         _  = z<s
<-trans (suc m) (suc n) (suc q)  (s<s m<n) (s<s n<q) = s<s (<-trans m n q m<n n<q)

-- Exercise trichotomy (practice)
-- Show that strict inequality satisfies a weak version of trichotomy,
-- in the sense that for any m and n that one of the following holds:
-- * m < n, * m ≡ n, or * m > n.
-- Define m > n to be the same as n < m. You will need a suitable data declaration, similar to that used for totality.
data Trich (m n : ℕ) : Set where

  lt :
    m < n
      ---------
    → Trich m n

  eq :
    n ≡ m
      ---------
    → Trich m n

  gt :
    n < m
      ---------
    → Trich m n

<-trichotomy : ∀ (m n : ℕ) → Trich m n
<-trichotomy    zero    zero = eq refl
<-trichotomy    zero (suc n) = lt z<s
<-trichotomy (suc m)    zero = gt z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n
...                              | lt m<n = lt (s<s m<n)
...                              | eq m≡n = eq (cong suc m≡n)
...                              | gt m>n = gt (s<s m>n)


-- Exercise +-mono-< (practice)
-- Show that addition is monotonic with respect to strict inequality.
-- As with inequality, some additional definitions may be required.
+-monoʳ-< : ∀ (n p q : ℕ)
  → p < q
    -------------
  → n + p < n + q
+-monoʳ-< zero    p q p<q  =  p<q
+-monoʳ-< (suc n) p q p<q  =  s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ (m n p : ℕ)
  → m < n
    -------------
  → m + p < n + p
+-monoˡ-< m n p m<n  rewrite +-comm m p | +-comm n p  = +-monoʳ-< p m n m<n

+-mono-< : ∀ (m n p q : ℕ)
  → m < n
  → p < q
  -------------
  → m + p < n + q
+-mono-< m n p q m<n p<q  =  <-trans (m + p) (n + p) (n + q) (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)


-- Exercise ≤-iff-< (recommended)
-- Show that suc m ≤ n implies m < n, and conversely.
≤-iff-<⃗ : ∀ (m n : ℕ)
  → suc m ≤ n
  ------------
  → m < n
≤-iff-<⃗ zero (suc n) _ = z<s
≤-iff-<⃗ (suc m) (suc n) (s≤s m≤n) = s<s (≤-iff-<⃗ m n m≤n)

≤-iff-<⃖ : ∀ (m n : ℕ)
  → m < n
  ------------
  → suc m ≤ n
≤-iff-<⃖ zero (suc n) _ = s≤s z≤n
≤-iff-<⃖ (suc m) (suc n) (s<s m<n) = s≤s (≤-iff-<⃖ m n m<n)

-- Exercise <-trans-revisited (practice)
-- Give an alternative proof that strict inequality is transitive,
-- using the relation between strict inequality and inequality and the fact that inequality is transitive.
suc< : ∀ (m n : ℕ) → suc m < n → m < n
suc< zero (suc n) (s<s m+1<n) = z<s
suc< (suc m) (suc n) (s<s m+1<n) = s<s (suc< m n m+1<n)

<-trans-revisited : (m n q : ℕ)
  → m < n
  → n < q
  ----------
  → m < q

<-trans-revisited m n q m<n n<q = suc< m q (≤-iff-<⃗ (suc m) q (≤-trans (≤-iff-<⃖ (suc m) (suc n) (s<s m<n)) (≤-iff-<⃖ n q n<q)))


-- Even and odd
-- As a further example, let’s specify even and odd numbers.
-- Inequality and strict inequality are binary relations,
-- while even and odd are unary relations, sometimes called predicates:

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
    ---------
    even zero

  suc  : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where

  suc  : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
  ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
  -----------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

-- Exercise o+o≡e (stretch)
-- Show that the sum of two odd numbers is even.
-- Exercise o+o≡e (stretch)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
  -----------
  → odd (m + n)
e+o≡o {m} {n} em on rewrite (+-comm m n) = o+e≡o on em

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  -----------
  → even (m + n)

o+o≡e {(suc x)} {(suc y)} (suc ex) (suc ey) = suc {(x + suc y)} (e+o≡o {x} {suc y} ex (suc ey))


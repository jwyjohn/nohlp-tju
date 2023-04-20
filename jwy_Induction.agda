import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

-- 加法结合律例子
_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

-- 加法结合律的证明
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

-- 加法交换律
-- 引理：加零的交换律
+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) =
  begin
    (suc m) + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc (m)
  ∎
-- 引理：suc 外推
+-suc : ∀ (m n : ℕ) → m + (suc n) ≡ suc (m + n)
+-suc zero n = refl
+-suc (suc m) n =
  begin
     (suc m) + (suc n)
   ≡⟨⟩
     suc (m + (suc n))
   ≡⟨ cong suc (+-suc m n) ⟩
     suc (suc (m + n))
   ∎
-- 证明加法交换律
+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero = +-identityʳ m
+-comm m (suc n) =
  begin
    m + (suc n)
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ∎

-- 第一个推论：重排定理
-- 我们可以随意应用结合律来重排括号
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ∎


-- 用改写来证明结合律
+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero    n p                          =  refl
+-assoc′ (suc m) n p  rewrite +-assoc′ m n p  =  refl

-- 使用改写证明交换律
+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- 练习：+-swap
-- 请证明对于所有的自然数 m、n 和 p，
-- m + (n + p) ≡ n + (m + p)
-- 成立。
-- [Tip] 无需归纳证明，只需应用前面满足结合律和交换律的结果即可。
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p
  rewrite (sym (+-assoc m n p))
  rewrite (+-comm m n)
  rewrite (+-assoc n m p) = refl

-- 练习 *-distrib-+
-- 请证明乘法对加法满足分配律，即对于所有的自然数 m、n 和 p，
-- (m + n) * p ≡ m * p + n * p
-- 成立。
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p =
  begin
    p + (m + n) * p
  ≡⟨ cong (p +_) (*-distrib-+ m n p) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + m * p) + n * p
  ∎

-- 练习 *-assoc
-- 请证明乘法满足结合律，即对于所有的自然数 m、n 和 p，
-- (m * n) * p ≡ m * (n * p)
-- 成立。
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p =
  begin
    (n + m * n) * p
  ≡⟨ *-distrib-+ n (m * n) p ⟩
    n * p + m * n * p
  ≡⟨ cong (n * p +_) (*-assoc m n p) ⟩
    n * p + m * (n * p)
  ∎

-- 练习 *-comm（实践）
-- 请证明乘法满足交换律，即对于所有的自然数 m 和 n，
-- m * n ≡ n * m
-- 成立。和加法交换律一样，你需要陈述并证明配套的引理。
*-zeroʳ : ∀ (m : ℕ) → m * 0 ≡ 0
*-zeroʳ zero = refl
*-zeroʳ (suc n) =
  begin
    n * 0
  ≡⟨ *-zeroʳ n ⟩
    0
  ∎

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-suc zero n = refl
*-suc (suc m) n =
  begin
    suc (n + m * suc n)
  ≡⟨ cong suc (cong (n +_) (*-suc m n)) ⟩
    suc (n + (m + m * n))
  ≡⟨ cong suc (+-swap n m (m * n)) ⟩
    suc (m + (n + m * n))
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m zero = *-zeroʳ m
*-comm m (suc n) =
  begin
    m * suc n
  ≡⟨ *-suc m n ⟩
    m + m * n
  ≡⟨ cong (m +_) (*-comm m n) ⟩
    m + n * m
  ∎


-- 练习 0∸n≡0（实践）
-- 请证明对于所有的自然数 n，
-- zero ∸ n ≡ zero
-- 成立。你的证明需要归纳法吗？
∸-gtz : ∀ (n : ℕ) → zero ∸ n ≡ zero
∸-gtz zero = refl
∸-gtz (suc n) = refl

-- 练习 +*^ （延伸）
-- 证明下列三条定律
-- m ^ (n + p) ≡ (m ^ n) * (m ^ p)  (^-distribˡ-+-*)
-- (m * n) ^ p ≡ (m ^ p) * (n ^ p)  (^-distribʳ-*)
-- (m ^ n) ^ p ≡ m ^ (n * p)        (^-*-assoc)
-- 对于所有 m、n 和 p 成立。

*-identityʳ : ∀ (m : ℕ) → m * 1 ≡ m
*-identityʳ zero = refl
*-identityʳ (suc m) = cong suc (*-identityʳ m)

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p
  rewrite (sym (*-assoc m n p))
  rewrite (*-comm m n)
  rewrite (*-assoc n m p) = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m n zero = 
  begin
    m ^ (n + zero)
  ≡⟨ cong (m ^_) (+-identityʳ n) ⟩
    m ^ n
  ≡⟨ sym (*-identityʳ (m ^ n)) ⟩
    (m ^ n) * 1
  ∎
^-distribˡ-+-* m n (suc p) = 
  begin
    m ^ (n + suc p)
  ≡⟨ cong (m ^_) (+-comm n (suc p)) ⟩
    m ^ (suc p + n)
  ≡⟨⟩
    m ^ (suc (p + n))
  ≡⟨⟩
    m * m ^ (p + n)
  ≡⟨ cong (m *_) (cong (m ^_) (+-comm p n)) ⟩
    m * m ^ (n + p)
  ≡⟨ cong (m *_) (^-distribˡ-+-* m n p) ⟩
    m * ((m ^ n) * (m ^ p))
  ≡⟨ *-swap m (m ^ n) (m ^ p) ⟩
    (m ^ n) * (m * (m ^ p))
  ∎

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ (m ^ p) * (n ^ p)
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) = 
  begin
    m * n * ((m * n) ^ p)
  ≡⟨ cong (m * n *_) (^-distribʳ-* m n p) ⟩
    m * n * ((m ^ p) * (n ^ p))
  ≡⟨ *-assoc m n ((m ^ p) * (n ^ p)) ⟩
    m * (n * ((m ^ p) * (n ^ p)))
  ≡⟨ cong  (m *_) (*-swap n (m ^ p) (n ^ p)) ⟩
    m * ((m ^ p) * (n * (n ^ p)))
  ≡⟨ sym (*-assoc m (m ^ p) (n * (n ^ p))) ⟩
    m * (m ^ p) * (n * (n ^ p))
  ∎

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero = 
  begin
    1
  ≡⟨⟩
    m ^ zero
  ≡⟨ cong (m ^_) (sym (*-zeroʳ n)) ⟩
    m ^ (n * zero)
  ∎
^-*-assoc m n (suc p) = 
  begin
    (m ^ n) * ((m ^ n) ^ p)
  ≡⟨ cong ((m ^ n) *_) (^-*-assoc m n p) ⟩
    (m ^ n) * m ^ (n * p)
  ≡⟨ sym (^-distribˡ-+-* m n (n * p)) ⟩
    m ^ (n + n * p)
  ≡⟨ cong (m ^_) (cong (n +_) (*-comm n p)) ⟩
    m ^ (n + p * n)
  ≡⟨⟩
    m ^ ((suc p) * n)
  ≡⟨ cong (m ^_) (*-comm (suc p) n) ⟩
    m ^ (n * suc p)
  ∎


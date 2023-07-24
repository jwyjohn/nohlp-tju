{-# OPTIONS --exact-split #-}
-- 定义自然数
-- ℕ is typed as \bN
-- ­→ is typed as \->
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- 练习 seven（实践）
-- 请写出 7 的完整定义。
seven : ℕ
seven = suc(suc(suc(suc(suc(suc(suc(zero)))))))

-- 导入模块
{-# BUILTIN NATURAL ℕ #-}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

-- 定义加法
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

-- 计算 2 + 3
-- ­≡ is typed as \==
_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- 展开为
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- 归纳步骤
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- 归纳步骤
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- 起始步骤
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- 简写为
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

-- 计算 3 + 4，将你的推导过程写成等式链，为 + 使用等式。
_ : 3 + 4 ≡ 7
_ = refl

-- 计算 3 + 4
_ : 3 + 4 ≡ 7
_ =
  begin
    3 + 4
  ≡⟨⟩    -- 展开为
    (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- 归纳步骤
    suc ((suc (suc zero)) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩    -- 归纳步骤
    suc (suc ((suc zero) + (suc (suc (suc (suc zero))))))
  ≡⟨⟩    -- 起始步骤
    suc (suc (suc (zero + (suc (suc (suc (suc zero)))))))
  ≡⟨⟩    -- 简写为
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ∎

-- 一旦我们定义了加法，我们就可以将乘法定义为重复的加法。
_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

-- 计算二乘三
_ =
  begin
    2 * 3
  ≡⟨⟩    -- 归纳步骤
    3 + (1 * 3)
  ≡⟨⟩    -- 归纳步骤
    3 + (3 + (0 * 3))
  ≡⟨⟩    -- 起始步骤
    3 + (3 + 0)
  ≡⟨⟩    -- 化简
    6
  ∎

-- 练习 _^_
-- 根据以下等式写出乘方的定义。
-- m ^ 0        =  1
-- m ^ (1 + n)  =  m * (m ^ n)

_^_ : ℕ → ℕ → ℕ
m ^ zero  =  1
m ^ (suc n) = m * (m ^ n)

-- 检查 3 ^ 4 是等于 81
_ : 3 ^ 4 ≡ 81
_ = refl


-- 饱和减法
-- 我们也可以定义减法。由于没有负的自然数，如果被减数比减数小， 我们就将结果取零。这种针对自然数的减法变种称作饱和减法（Monus，由 minus 修改而来）。
-- 饱和减法是我们首次在定义中对两个参数都使用模式匹配
-- ∸ is typed as \.-
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

-- 计算三减二
_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

-- 计算二减去三
_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

-- 写在文件的开始可以让 Agda 在不同情况相互重叠时产生一个错误， 有些时候这会有帮助。我们会在逻辑连接符部分 展示一个这样的例子。
-- {-# OPTIONS --exact-split #-}

_ : 5 ∸ 3 ≡ 2
_ = refl
_ : 3 ∸ 5 ≡ 0
_ = refl

-- 优先级
-- 值越大，优先级越高
infixl 6  _+_  _∸_
infixl 7  _*_

-- test
_∔_ : ℕ → ℕ → ℕ
zero ∔ n = n
suc m ∔ n = suc (m + n)


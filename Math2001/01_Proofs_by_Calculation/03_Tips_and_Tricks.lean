/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.3: Tips and tricks

Exercise: choose some of these examples and type out the whole proofs printed in the text as Lean
proofs. -/


-- Example 1.3.1
example {a b : ℤ} (h1 : a = 2 * b + 5) (h2 : b = 3) : a = 11 :=
  calc
    a = 2 * b + 5 := by rw [h1]
    _ = 2 * 3 + 5 := by rw [h2]
    _ = 11 := by ring

-- Example 1.3.2
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring

-- Example 1.3.3
example {a b : ℝ} (h1 : a - 5 * b = 4) (h2 : b + 2 = 3) : a = 9 :=
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * b := by rw [h1]
    _ = 4 + 5 * (b + 2 - 2) := by ring
    _ = 4 + 5 * (3 - 2) := by rw [h2]
    _ = 9 := by ring

-- Example 1.3.4
-- a)
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = (3 * w + 1 - 1) / 3 := by ring
    _ = (4 - 1) / 3 := by rw [h1]
    _ = 1 := by ring

-- В простейших случаях
-- надо начать с того, что написать справа от равенства
-- левую часть одной из имеющихся гипотез (3 * w + 1).
-- Затем нужно придумать как сделать, чтобы это равнялось
-- левой части равенства цели (w).

-- b)
example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 :=
  calc
    w = (3 * w + 1) / 3 - 1 / 3 := by ring
    _ = 4 / 3 - 1 / 3 := by rw [h1]
    _ = 1 := by ring

-- Example 1.3.5
example {x : ℤ} (h1 : 2 * x + 3 = x) : x = -3 :=
  calc
    x = 2 * x + 3 - 3 - x := by ring
    _ = x - 3 - x := by rw [h1]
    _ = -3 := by ring

-- ^ Снова пишем сразу левую часть равенства гипотезы (2 * x + 3),
-- придумываем что-то, чтобы всё выражение было равно левой части цели
-- (- 3 - x) и "обосновываем" переход (by ring).

-- Example 1.3.6
-- a)
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x = (2 * x - y) + y - x + 1 - 1 := by ring
    _ = (4 + y - x + 1) - 1 := by rw [h1]
    _ = 4 + (y - x + 1 - 1) := by ring
    _ = 4 + (2 - 1) := by rw [h2]
    _ = 5 := by ring

-- Иногда можно выбрать любую гипотезу для первого "перехода".

-- b)
example {x y : ℤ} (h1 : 2 * x - y = 4) (h2 : y - x + 1 = 2) : x = 5 :=
  calc
    x = (y - x + 1) + (2 * x - y) - 1 := by ring
    _ = 2 + 4 - 1 := by rw [h1, h2]
    _ = 5 := by ring

-- Example 1.3.7
-- Иногда нужно придумать как сложить или вычесть несколько гипотез,
-- чтобы выполнить "переход" (переписывание) по их равенствам.
--
-- Тут идея доказательства в том, чтобы избавиться от одной из переменных.
-- Для этого мы вычитаем или складываем модифицированные левые части гипотез.
example {u v : ℚ} (h1 : u + 2 * v = 4) (h2 : u - 2 * v = 6) : u = 5 :=
  calc
    u = ((u + 2 * v) + (u - 2 * v)) / 2 := by ring
    _ = (4 + (u - 2 * v)) / 2 := by rw [h1]
    _ = (4 + 6) / 2 := by rw [h2]
    _ = 5 := by ring

-- Example 1.3.8
-- Тут тоже складываем гипотезы, чтобы избавиться от одной из переменных.
-- Разница только в том, что мы домножаем h1 на 3, чтобы получить 3 * y.
example {x y : ℝ} (h1 : x + y = 4) (h2 : 5 * x - 3 * y = 4) : x = 2 :=
  calc
    -- (3 * h1 + h2) / 8 = (3 * 4 + 4) / 8 = 16 / 8 = 2
    x = (3 * (x + y) + (5 * x - 3 * y)) / 8 := by ring
    _ = (3 * 4 + 4) / 8 := by rw [h1, h2]
    _ = 2 := by ring

-- Example 1.3.9
-- Тут нужно заметить, что
-- (a - 3) ^ 2 = (2 * b) ^ 2 = 4 * b ^ 2
example {a b : ℚ} (h1 : a - 3 = 2 * b)
        : a ^ 2 - a + 3 = 4 * b ^ 2 + 10 * b + 9 :=
  calc
    a ^ 2 - a + 3 = a ^ 2 - (a - 3) := by ring
    _ = (a - 3) ^ 2 + 2 * 3 * a - 3 ^ 2 - a + 3 := by ring
    _ = (a - 3) ^ 2 + 5 * a - 6 := by ring
    _ = (a - 3) ^ 2 + 5 * (a - 3 + 3) - 6 := by ring
    _ = (2 * b) ^ 2 + 5 * (2 * b + 3) - 6 := by rw [h1]
    _ = (2 * b) ^ 2 + 10 * b + 9 := by ring
    _ = 4 * b ^ 2 + 10 * b + 9 := by ring

-- Example 1.3.10
example {z : ℝ} (h1 : z ^ 2 - 2 = 0)
        : z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = 3 :=
  calc
    z ^ 4 - z ^ 3 - z ^ 2 + 2 * z + 1 = (z ^ 2 - z + 1) * (z ^ 2 - 2) + 3 := by ring
    _ = (z ^ 2 - z + 1) * 0 + 3 := by rw [h1]
    _ = 3 := by ring

/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/

-- 1.
example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 :=
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4 * 3 - 3 := by rw [h1]
    _ = 9 := by ring

-- 2.
example {a b : ℤ} (h : a - b = 0) : a = b :=
  calc
    a = a - b + b := by ring
    _ = 0 + b := by rw [h]
    _ = b := by ring

-- 3.
example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 :=
  calc
    x = x - 3 * y + 3 * y := by ring
    _ = 5 + 3 * y := by rw [h1]
    _ = 5 + 3 * 3 := by rw [h2]
    _ = 14 := by ring

-- 4.
example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 :=
  calc
    p = p - 2 * q + 2 * q := by ring
    _ = 1 + 2 * q := by rw [h1]
    _ = 1 + 2 * (-1) := by rw [h2]
    _ = -1 := by ring

-- 5.
example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 :=
  calc
    x = (x + 2 * y) - 2 * (y + 1) + 2 := by ring
    _ = 3 - 2 * (y + 1) + 2 := by rw [h2]
    _ = 3 - 2 * 3 + 2 := by rw [h1]
    _ = -1 := by ring

-- 6.
example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 :=
  calc
    p = (p + 4 * q) - 4 * (q - 1) - 4 := by ring
    _ = 1 - 4 * (q - 1) - 4 := by rw [h1]
    _ = 1 - 4 * 2 - 4 := by rw [h2]
    _ = -11 := by ring

-- 7.
example {a b c : ℝ}
        (h1 : a + 2 * b + 3 * c = 7)
        (h2 : b + 2 * c = 3)
        (h3 : c = 1)
        : a = 2 :=
  calc
    a = (a + 2 * b + 3 * c) - 2 * (b + 2 * c) + c := by ring
    _ = 7 - 2 * (b + 2 * c) + c := by rw [h1]
    _ = 7 - 2 * 3 + c := by rw [h2]
    _ = 7 - 2 * 3 + 1 := by rw [h3]
    _ = 2 := by ring

-- 8.
example {u v : ℚ} (h1 : 4 * u + v = 3) (h2 : v = 2) : u = 1 / 4 :=
  calc
    u = ((4 * u + v) - v) / 4 := by ring
    _ = (3 - v) / 4 := by rw [h1]
    _ = (3 - 2) / 4 := by rw [h2]
    _ = 1 / 4 := by ring

-- 9.
example {c : ℚ} (h1 : 4 * c + 1 = 3 * c - 2) : c = -3 :=
  calc
    c = (4 * c + 1) - (3 * c - 2) - 3 := by ring
    _ = (3 * c - 2) - (3 * c - 2) - 3 := by rw [h1]
    _ = -3 := by ring

-- 10.

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  -- p + 4 + 3 * (5 * p - 3) - 5 * (3 * p + 1)
  -- p + 4 + 15 * p - 9 - 15 * p + 5
  calc
    p = p + 4 + 3 * (5 * p - 3) - 5 * (3 * p + 1 - 2) := by ring
    _ = p + 4 + 3 * (5 * p - 3) - 5 * (5 * p - 3 - 2) := by rw [h1]
    _ = p + 4 + 15 * p - 9 - 25 * p + 25 := by ring
    _ = (21 - 9 * p) - 1 := by ring
    _ = 2 := by sorry

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  -- p + 4 + 3 * (5 * p - 3) - 5 * (3 * p + 1)
  -- p + 4 + 15 * p - 9 - 15 * p + 5
  calc
    p = p + 4 + 3 * (5 * p - 3) - 5 * (3 * p - 1) := by ring
    _ = p + 4 + 3 * (3 * p + 1) - 5 * (3 * p - 1) := by rw [h1]
    _ = p + 4 + 9 * p + 3 - 15 * p + 5 := by ring
    _ = 12 - 5 * p := by ring
    _ = 2 := by sorry

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  -- 2 * (5 * p - 3) - 3 * (3 * p + 1)
  calc
    p = 2 * (5 * p - 3) - 3 * (3 * p + 1) + 9 := by ring
    _ = 10 * p - 6 - 9 * p - 3 + 9 := by ring
    _ = 2 := by sorry

example {p : ℝ} (h1 : 5 * p - 3 = 3 * p + 1) : p = 2 :=
  calc
    p = (5 * p - 3) - (4 * p - 3) := by ring
    _ = (5 * p - 3) - (3 * p + 1) - p + 4 := by ring
    _ = (3 * p + 1) - (3 * p + 1) - p + 4 := by rw [h1]
    _ = 4 - p := by ring
    _ = 4 - p + (5 * p - 3) - (5 * p - 3) := by ring
    _ = 4 - p + (5 * p - 3) - (3 * p + 1) := by rw [h1]
    _ = 2 := by sorry

-- 11.
example {x y : ℤ} (h1 : 2 * x + y = 4) (h2 : x + y = 1) : x = 3 :=
  calc
    x = (x + y) + (2 * x + y) - 2 * (x + y) := by ring
    _ = (x + y) + 4 - 2 * (x + y) := by rw [h1]
    _ = 1 + 4 - 2 * 1 := by rw [h2]
    _ = 3 := by ring

-- 12.
example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 :=
  calc
    a = (a + 2 * b) + 2 * (a - b) - 2 * a - 2 * b + 2 * b := by ring
    _ = 4 + 2 * 1 - 2 * a - 2 * b + 2 * b := by rw [h1, h2]
    _ = 6 - ((a + 2 * b) + a - 2 * b) := by ring
    _ = 2 := by sorry

-- 13.
example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 :=
  calc
    u ^ 2 + 3 * u + 1 = u ^ 2 + 2 * u + 1 + u := by ring
    _ = (u + 1) ^ 2 + u := by ring
    _ = v ^ 2 + u := by rw [h1]
    _ = v ^ 2 + (u + 1) - 1 := by ring
    _ = v ^ 2 + v - 1 := by rw [h1]
    _ = v ^ 2 + v - 1 := by ring

-- 14.
example {t : ℚ} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 :=
  calc
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 =
      (t ^ 4 - 8 * t ^ 2 + 16) + 5 * t ^ 2 - 18 + 3 * t ^ 3 - 2 * t := by ring
    _ = (t ^ 2 - 4) ^ 2 + 5 * t ^ 2 - 18 + 3 * t ^ 3 - 2 * t := by ring
    _ = 0 ^ 2 + 5 * t ^ 2 - 18 + 3 * t ^ 3 - 2 * t := by rw [ht]
    _ = 3 * t ^ 3 - 2 * t + 5 * t ^ 2 - 18 := by ring
    _ = t * (3 * t ^ 2 - 2) + (5 * t ^ 2 - 18) := by ring
    _ = t * ((3 * t ^ 2 - 3 * 4) + 10) + ((5 * t ^ 2 - 5 * 4) + 2) := by ring
    _ = t * (3 * (t ^ 2 - 4) + 10) + ((5 * (t ^ 2 - 4)) + 2) := by ring
    _ = t * (3 * 0 + 10) + ((5 * 0) + 2) := by rw [ht]
    _ = t * 10 + 2 := by ring
    _ = 10 * t + 2 := by rw [mul_comm]

-- a ^ 3 - 3 * (a ^ 2) * b + 3 * a * (b ^ 2) + b ^ 3
-- a ^ 4 - 4 * (a ^ 3) * b + 6 * (a ^ 2) * (b ^ 2) - 4 * a * (b ^ 3) + b ^ 4

-- 15.
example {x y : ℝ} (h1 : x + 3 = 5) (h2 : 2 * x - y * x = 0) : y = 2 :=
  calc
    y = 2 * ((x + 3) - 3) - y * ((x + 3) - 3) - 2 * x + y * x + y := by ring
    _ = 2 * (5 - 3) - y * (5 - 3) - 2 * x + y * x + y := by rw [h1]
    _ = 4 - y * 2 - (2 * x - y * x) + y := by ring
    _ = 4 - y * 2 - 0 + y := by rw [h2]
    _ = 4 - y := by ring
    _ = 2 := by sorry

-- 16.
example {p q r : ℚ}
        (h1 : p + q + r = 0)
        (h2 : p * q + p * r + q * r = 2)
        : p ^ 2 + q ^ 2 + r ^ 2 = -4 :=
  calc
    p ^ 2 + q ^ 2 + r ^ 2 =
      (p + q + r) ^ 2 - 2 * (p * q + p * r + q * r) := by ring
    _ = 0 ^ 2 - 2 * 2 := by rw [h1, h2]
    _ = -4 := by ring

    -- = (p + q + r) ^ 2
    -- = (p + q + r) * (p + q + r)
    -- = (p ^ 2 + p * q + p * r) +
    --   (q * p + q ^ 2 + q * r) +
    --   (r * p + r * q + r ^ 2)
    --
    -- = (p ^ 2 + q ^ 2 + r ^ 2) +
    --   (p * q + p * r) +
    --   (p * q + q * r) +
    --   (p * r + q * r)
    --
    -- = (p ^ 2 + q ^ 2 + r ^ 2) + 2 * (p * q + p * r + q * r)

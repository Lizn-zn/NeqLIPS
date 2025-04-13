import Mathlib

import Math.Scale_Cauchy_Schwarz

open Real

local macro_rules | `($x / $y)   => `(HDiv.hDiv ($x : ℝ) ($y : ℝ))

-- ========================== Jensen inequalities ==========================

section Scale_Jensen_2vars

/-- The Basic form Jensen_sqrt : (√u + √v) / 2 ≤ √((u + v) / 2) -/
theorem Jensen_sqrt_2vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) : (sqrt (u) + sqrt (v)) / 2 ≤ sqrt ((u + v) / 2) := by
  sorry

theorem Jensen_sqrt_left_2vars (u v k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hk : k ≥ 0) (h : k * (sqrt 2) * sqrt (u + v) + l ≤ right) :
  k * (sqrt (u) + sqrt (v)) + l ≤ right := by
  suffices sqrt (u) + sqrt (v) ≤ (sqrt 2) * sqrt (u + v) by nlinarith
  have h := Jensen_sqrt_2vars u v
  simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 2) (b := (sqrt (u) + sqrt (v))) (c := (sqrt 2) * sqrt (u + v))]
  convert h using 1
  linarith
  rw [show (2:ℝ) = sqrt 2 ^2 by norm_num]; field_simp; ring_nf; simp [sq_sqrt]; linarith
  positivity

theorem Jensen_sqrt_right_2vars (u v k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hk : k ≥ 0) (h : left ≤ k * ((sqrt (u) + sqrt (v)) / (sqrt 2)) + l) :
  left ≤ k * sqrt (u + v) + l := by
  suffices (sqrt (u) + sqrt (v)) / (sqrt 2) ≤ sqrt (u + v) by nlinarith
  have h := Jensen_sqrt_2vars u v
  simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / sqrt 2) (b := (sqrt (u) + sqrt (v)) / (sqrt 2)) (c := sqrt (u + v))]
  convert h using 1
  field_simp; ring_nf;
  positivity

end Scale_Jensen_2vars

section Scale_Jensen_3vars

/-- The basic form of Jensen_sqrt : (√u + √v + √w) / 3 ≤ √((u + v + w) / 3) -/
theorem Jensen_sqrt_3vars (u v w : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) : (sqrt (u) + sqrt (v) + sqrt (w)) / 3 ≤ sqrt ((u + v + w) / 3) := by
  sorry

theorem Jensen_sqrt_left_3vars (u v w k l right : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0) (h : k * (sqrt 3) * sqrt (u + v + w) + l ≤ right) : k * (sqrt (u) + sqrt (v) + sqrt (w)) + l ≤ right := by
  suffices sqrt (u) + sqrt (v) + sqrt (w) ≤ (sqrt 3) * sqrt (u + v + w) by nlinarith
  have h := Jensen_sqrt_3vars u v w
  simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 3) (b := (sqrt (u) + sqrt (v) + sqrt (w))) (c := (sqrt 3) * sqrt (u + v + w))]
  convert h using 1
  linarith
  rw [show (3:ℝ) = sqrt 3 ^2 by norm_num]; field_simp; ring_nf; simp [sq_sqrt]; linarith
  positivity

theorem Jensen_sqrt_right_3vars (u v w k l left : ℝ) (hu : u ≥ 0) (hv : v ≥ 0) (hw : w ≥ 0) (hk : k ≥ 0) (h : left ≤ k * ((sqrt (u) + sqrt (v) + sqrt (w)) / (sqrt 3)) + l) : left ≤ k * sqrt (u + v + w) + l := by
  suffices (sqrt (u) + sqrt (v) + sqrt (w)) / (sqrt 3) ≤ sqrt (u + v + w) by nlinarith
  have h := Jensen_sqrt_3vars u v w
  simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / sqrt 3) (b := (sqrt (u) + sqrt (v) + sqrt (w)) / (sqrt 3)) (c := sqrt (u + v + w))]
  convert h using 1
  field_simp; ring_nf;
  positivity



/-- The basic form of Jensen_sqrt_div : (1/√u + 1/√v + 1/√w) / 3 ≥ 1/√((u + v + w) / 3) -/
theorem Jensen_sqrt_div_3vars (u v w : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) : 1 / sqrt ((u + v + w) / 3) ≤ (1 / sqrt u + 1 / sqrt v + 1 / sqrt w) / 3 := by
  sorry

theorem Jensen_sqrt_div_left_3vars (u v w k l right : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k ≥ 0) (h : k * ((1 / sqrt u + 1 / sqrt v + 1 / sqrt w) / (sqrt 27)) + l ≤ right) : k * (1 / sqrt (u + v + w)) + l ≤ right := by
  suffices 1 / sqrt (u + v + w) ≤ (1 / sqrt u + 1 / sqrt v + 1 / sqrt w) / sqrt (27) by nlinarith
  have h := Jensen_sqrt_div_3vars u v w
  simp [*] at h
  rw [<- mul_le_mul_right (a := sqrt 3) (b := 1 / sqrt (u + v + w)) (c := (1 / sqrt u + 1 / sqrt v + 1 / sqrt w) / (sqrt 27))]
  convert h using 1
  field_simp; ring_nf;
  rw [show (27:ℝ) = 3 * 3 ^2 by norm_num]; field_simp; ring_nf;
  positivity

theorem Jensen_sqrt_div_right_3vars (u v w k l left : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k ≥ 0) (h : left ≤ k * (1 / sqrt ((u + v + w) / 27)) + l) : left ≤ k * (1 / sqrt u + 1 / sqrt v + 1 / sqrt w) + l := by
  suffices 1 / sqrt ((u + v + w) / 27) ≤ (1 / sqrt u + 1 / sqrt v + 1 / sqrt w) by nlinarith
  have h := Jensen_sqrt_div_3vars u v w
  simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 3) (b := 1 / sqrt ((u + v + w) / 27)) (c := 1 / sqrt u + 1 / sqrt v + 1 / sqrt w)]
  convert h using 1
  rw [show (27:ℝ) = 3 * 3 ^2 by norm_num]; field_simp; ring_nf;
  field_simp;
  positivity


/-- The basic format of Jensen_dick_div : ((i1*u) / (i2*u^2+j1*u+j2) + (i1*v) / (i2*v^2+j1*v+j2) + (i1*w) / (i2*w^2+j1*w+j2)) / 3 ≤ i1*(u+v+w) / 3 / (i2*((u+v+w)/3)^2 + j1*(u+v+w)/3 + j2) -/
theorem Jensen_dick_div (u v w i1 i2 j1 j2) (hi1 : i1 > 0) (hi2 : i2 > 0) (hj2 : j2 ≥ 0)
  (h1 : i2 * u ^ 2 + j1 * u + j2 > 0)
  (h2 : i2 * v ^ 2 + j1 * v + j2 > 0)
  (h3 : i2 * w ^ 2 + j1 * w + j2 > 0) :
  ((i1 * u) / (i2 * u ^ 2 + j1 * u + j2) + (i1 * v) / (i2 * v^2 + j1 * v + j2) + (i1 * w) / (i2 * w ^ 2 + j1 * w + j2)) / 3 ≤ (i1 * (u + v + w) / 3) / (i2 * ((u + v + w) / 3) ^ 2 + j1 * (u + v + w) / 3 + j2) :=
  by sorry

theorem Jensen_dick_div_left_3vars (u v w i1 i2 j1 j2 k l right : ℝ) (hi1 : i1 > 0) (hi2 : i2 > 0) (hj2 : j2 ≥ 0) (hk : k ≥ 0)
  (h1 : i2 * u ^ 2 + j1 * u + j2 > 0)
  (h2 : i2 * v ^ 2 + j1 * v + j2 > 0)
  (h3 : i2 * w ^ 2 + j1 * w + j2 > 0)
  (h : k * (i1 * (u + v + w) / (i2 * ((u + v + w) / 3) ^ 2 + j1 * (u + v + w) / 3 + j2)) + l ≤ right) :
  k * ((i1 * u) / (i2 * u ^ 2 + j1 * u + j2) + (i1 * v) / (i2 * v^2 + j1 * v + j2) + (i1 * w) / (i2 * w ^ 2 + j1 * w + j2)) + l ≤ right := by
  suffices (i1 * u) / (i2 * u ^ 2 + j1 * u + j2) + (i1 * v) / (i2 * v^2 + j1 * v + j2) + (i1 * w) / (i2 * w ^ 2 + j1 * w + j2) ≤ i1 * (u + v + w) / (i2 * ((u + v + w) / 3) ^ 2 + j1 * (u + v + w) / 3 + j2) by nlinarith
  rw [<- mul_le_mul_right (a := 1 / 3)]
  have h := Jensen_dick_div u v w i1 i2 j1 j2 hi1 hi2 hj2 h1 h2 h3
  convert h using 1
  field_simp [*]; ring_nf;
  positivity

theorem Jensen_dick_div_right_3vars (u v w i1 i2 j1 j2 k l left : ℝ) (hi1 : i1 > 0) (hi2 : i2 > 0) (hj2 : j2 ≥ 0) (hk : k ≥ 0)
  (h1 : i2 * u ^ 2 + j1 * u + j2 > 0)
  (h2 : i2 * v ^ 2 + j1 * v + j2 > 0)
  (h3 : i2 * w ^ 2 + j1 * w + j2 > 0)
  (h : left ≤ k * ((i1 * u) / (i2 * u ^ 2 + j1 * u + j2) + (i1 * v) / (i2 * v^2 + j1 * v + j2) + (i1 * w) / (i2 * w ^ 2 + j1 * w + j2)) + l) :
  left ≤ k * (i1 * (u + v + w) / (i2 * ((u + v + w)) ^ 2 / 9 + j1 * (u + v + w) / 3 + j2)) + l := by
  suffices (i1 * u) / (i2 * u ^ 2 + j1 * u + j2) + (i1 * v) / (i2 * v^2 + j1 * v + j2) + (i1 * w) / (i2 * w ^ 2 + j1 * w + j2) ≤ i1 * (u + v + w) / (i2 * ((u + v + w)) ^ 2 / 9 + j1 * (u + v + w) / 3 + j2) by nlinarith
  rw [<- mul_le_mul_right (a := 1 / 3)]
  have h := Jensen_dick_div u v w i1 i2 j1 j2 hi1 hi2 hj2 h1 h2 h3
  convert h using 1
  field_simp [*]; ring_nf;
  positivity


/-- General Jensen for power r, i.e. x ^ r where (1) Rlt1 (2) Rgt1 -/
theorem Jensen_pow_Rlt1_3vars (u v w r : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hr : r > 0) (hr' : 1 - r > 0)  : (u ^ r + v ^ r + w ^ r) / 3 ≤ ((u + v + w) / 3) ^ r := by
  sorry

theorem Jensen_pow_Rlt1_left_3vars (u v w r k l right : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hr : r > 0) (hr' : 1 - r > 0) (hk : k ≥ 0)
  (h : k * (3 * ((u + v + w) / 3) ^ r) + l ≤ right) :
  k * (u ^ r + v ^ r + w ^ r) + l ≤ right := by
  suffices u ^ r + v ^ r + w ^ r ≤ 3 * ((u + v + w) / 3) ^ r by nlinarith
  rw [<- mul_le_mul_right (a := 1 / 3)]
  have h := Jensen_pow_Rlt1_3vars u v w r hu hv hw hr hr'
  convert h using 1
  field_simp [*]; ring_nf;
  positivity

theorem Jensen_pow_Rlt1_right_3vars (u v w r k l left : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hr : r > 0) (hr' : 1 - r > 0) (hk : k ≥ 0)
  (h : left ≤ k * ((u ^ r + v ^ r + w ^ r) / 3) + l) :
  left ≤ k * ((u + v + w) / 3) ^ r + l := by
  suffices (u ^ r + v ^ r + w ^ r) / 3 ≤ ((u + v + w) / 3) ^ r by nlinarith
  exact Jensen_pow_Rlt1_3vars u v w r hu hv hw hr hr'

theorem Jensen_pow_Rgt1_3vars (u v w r : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hr : r > 1) : ((u + v + w) / 3) ^ r ≤ (u ^ r + v ^ r + w ^ r) / 3 := by
  sorry

theorem Jensen_pow_Rgt1_left_3vars (u v w r k l right : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hr : r > 1) (hk : k ≥ 0)
  (h :  k * ((u ^ r + v ^ r + w ^ r) / 3) + l ≤ right) :
  k * ((u + v + w) / 3) ^ r + l ≤ right := by
  suffices (u ^ r + v ^ r + w ^ r) / 3 ≥ ((u + v + w) / 3) ^ r by nlinarith
  exact Jensen_pow_Rgt1_3vars u v w r hu hv hw hr

theorem Jensen_pow_Rgt1_right_3vars (u v w r k l left : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hr : r > 1) (hk : k ≥ 0)
  (h : left ≤ k * (3 * ((u + v + w) / 3) ^ r) + l) :
  left ≤ k * (u ^ r + v ^ r + w ^ r) + l := by
  suffices 3 * ((u + v + w) / 3) ^ r ≤ (u ^ r + v ^ r + w ^ r) by nlinarith
  rw [<- mul_le_mul_right (a := 1 / 3)]
  have h := Jensen_pow_Rgt1_3vars u v w r hu hv hw hr
  convert h using 1
  field_simp [*]; ring_nf;
  field_simp


/-- The Basic form Jensen_square_div : (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2) / 3 ≥ 9 / (u + v + w) ^ 2 -/
theorem Jensen_square_div_3vars (u v w : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) : 9 / (u + v + w) ^ 2 ≤ (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2) / 3 := by
  sorry

theorem Jensen_square_div_left_3vars (u v w k l right : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k > 0) (h : k * (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2) + l ≤ right) : k * (27 / (u + v + w) ^ 2) + l ≤ right := by
  suffices 27 / (u + v + w) ^ 2 ≤ (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2) by nlinarith
  have h := Jensen_square_div_3vars u v w
  simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 3) (b := 27 / (u + v + w) ^ 2) (c := (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2))]
  convert h using 1
  field_simp; linarith;
  field_simp; linarith

theorem Jensen_square_div_right_3vars (u v w k l left : ℝ) (hu : u > 0) (hv : v > 0) (hw : w > 0) (hk : k > 0) (h : left ≤ k * (1 / (u + v + w) ^ 2) + l) : left ≤ k * (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2) / 27 + l := by
  suffices 1 / (u + v + w) ^ 2 ≤ (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2) / 27 by nlinarith
  have h := Jensen_square_div_3vars u v w
  simp [*] at h
  rw [<- mul_le_mul_right (a := 9) (b := 1 / (u + v + w) ^ 2) (c := (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2) / 27) ]
  convert h using 1
  field_simp;
  field_simp; linarith;
  positivity

end Scale_Jensen_3vars

section Scale_Jensen_4vars

/-- General Jensen for power r, i.e. x ^ r where (1) Rlt1 (2) Rgt1 -/
theorem Jensen_pow_Rlt1_4vars (u1 u2 u3 u4 r : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hr : r > 0) (hr' : 1 - r > 0)  : (u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) / 4 ≤ ((u1 + u2 + u3 + u4) / 4) ^ r := by
  sorry

theorem Jensen_pow_Rlt1_left_4vars (u1 u2 u3 u4 r k l right : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hr : r > 0) (hr' : 1 - r > 0) (hk : k ≥ 0)
  (h : k * (4 * ((u1 + u2 + u3 + u4) / 4) ^ r) + l ≤ right) :
  k * (u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) + l ≤ right := by
  suffices u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r ≤ 4 * ((u1 + u2 + u3 + u4) / 4) ^ r by nlinarith
  rw [<- mul_le_mul_right (a := 1 / 4)]
  have h := Jensen_pow_Rlt1_4vars u1 u2 u3 u4 r hu1 hu2 hu3 hu4 hr hr'
  convert h using 1
  field_simp [*]; ring_nf;
  positivity

theorem Jensen_pow_Rlt1_right_4vars (u1 u2 u3 u4 r k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hr : r > 0) (hr' : 1 - r > 0) (hk : k ≥ 0)
  (h : left ≤ k * ((u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) / 4) + l) :
  left ≤ k * ((u1 + u2 + u3 + u4) / 4) ^ r + l := by
  suffices (u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) / 4 ≤ ((u1 + u2 + u3 + u4) / 4) ^ r by nlinarith
  exact Jensen_pow_Rlt1_4vars u1 u2 u3 u4 r hu1 hu2 hu3 hu4 hr hr'

theorem Jensen_pow_Rgt1_4vars (u1 u2 u3 u4 r : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hr : r > 1) : ((u1 + u2 + u3 + u4) / 4) ^ r ≤ (u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) / 4 := by
  sorry

theorem Jensen_pow_Rgt1_left_4vars (u1 u2 u3 u4 r k l right : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hr : r > 1) (hk : k ≥ 0)
  (h :  k * ((u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) / 4) + l ≤ right) :
  k * ((u1 + u2 + u3 + u4) / 4) ^ r + l ≤ right := by
  suffices (u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) / 4 ≥ ((u1 + u2 + u3 + u4) / 4) ^ r by nlinarith
  exact Jensen_pow_Rgt1_4vars u1 u2 u3 u4 r hu1 hu2 hu3 hu4 hr

theorem Jensen_pow_Rgt1_right_4vars (u1 u2 u3 u4 r k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hr : r > 1) (hk : k ≥ 0)
  (h : left ≤ k * (4 * ((u1 + u2 + u3 + u4) / 4) ^ r) + l) :
  left ≤ k * (u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) + l := by
  suffices 4 * ((u1 + u2 + u3 + u4) / 4) ^ r ≤ (u1 ^ r + u2 ^ r + u3 ^ r + u4 ^ r) by nlinarith
  rw [<- mul_le_mul_right (a := 1 / 4)]
  have h := Jensen_pow_Rgt1_4vars u1 u2 u3 u4 r hu1 hu2 hu3 hu4 hr
  convert h using 1
  field_simp [*]; ring_nf;
  field_simp


/-- The Basic form Jensen_square_div : (1 / u ^ 2 + 1 / v ^ 2 + 1 / w ^ 2 + 1 / z ^ 2) / 4 ≥ 16 / (u + v + w + z) ^ 2 -/
theorem Jensen_square_div_4vars (u1 u2 u3 u4 : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) : 16 / (u1 + u2 + u3 + u4) ^ 2 ≤ (1 / u1 ^ 2 + 1 / u2 ^ 2 + 1 / u3 ^ 2 + 1 / u4 ^ 2) / 4 := by
  sorry

theorem Jensen_square_div_left_4vars (u1 u2 u3 u4 k l right : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hk : k > 0)
  (h : k * (1 / u1 ^ 2 + 1 / u2 ^ 2 + 1 / u3 ^ 2 + 1 / u4 ^ 2) + l ≤ right) :
  k * (64 / (u1 + u2 + u3 + u4) ^ 2) + l ≤ right := by
  suffices 64 / (u1 + u2 + u3 + u4) ^ 2 ≤ (1 / u1 ^ 2 + 1 / u2 ^ 2 + 1 / u3 ^ 2 + 1 / u4 ^ 2) by nlinarith
  have h := Jensen_square_div_4vars u1 u2 u3 u4
  simp [*] at h
  rw [<- mul_le_mul_right (a := 1 / 4) (b := 64 / (u1 + u2 + u3 + u4) ^ 2) (c := (1 / u1 ^ 2 + 1 / u2 ^ 2 + 1 / u3 ^ 2 + 1 / u4 ^ 2))]
  convert h using 1
  field_simp; linarith
  field_simp; linarith

theorem Jensen_square_div_right_4vars (u1 u2 u3 u4 k l left : ℝ) (hu1 : u1 > 0) (hu2 : u2 > 0) (hu3 : u3 > 0) (hu4 : u4 > 0) (hk : k > 0)
  (h : left ≤ k * (1 / (u1 + u2 + u3 + u4) ^ 2) + l) :
  left ≤ k * (1 / u1 ^ 2 + 1 / u2 ^ 2 + 1 / u3 ^ 2 + 1 / u4 ^ 2) / 64 + l := by
  suffices 1 / (u1 + u2 + u3 + u4) ^ 2 ≤ (1 / u1 ^ 2 + 1 / u2 ^ 2 + 1 / u3 ^ 2 + 1 / u4 ^ 2) / 64 by nlinarith
  have h := Jensen_square_div_4vars u1 u2 u3 u4
  simp [*] at h
  rw [<- mul_le_mul_right (a := 16) (b := 1 / (u1 + u2 + u3 + u4) ^ 2) (c := (1 / u1 ^ 2 + 1 / u2 ^ 2 + 1 / u3 ^ 2 + 1 / u4 ^ 2) / 64)]
  convert h using 1
  field_simp;
  field_simp; linarith;
  positivity

end Scale_Jensen_4vars

module

public import ArithmeticTriangles.FiniteTotients

/-!
# A checked table of small cosine degrees

Seven bits suffice for each of the 232 entries. Packing the table into a
natural number makes repeated lookup cheap for kernel reduction. The equality
with Euler's product formula is itself proved by exact kernel computation.
-/

@[expose] public section
namespace ArithmeticTriangles

/-- The values φ(2n)/2 for n<232; the degree search uses only n≥11. -/
def smallCosineDegree (n : ℕ) : ℕ :=
  (353714020699750859203776079104352094245972502315608661948508592942771500630663879607065812399873948563815610665764324559589686617632730497491140197936531204249099368301683890654169310652416489615005791144090501123779249149440461407676602490736285667140891117638065647058094329479292619195885350120954532490762443525909893508854038934568453696712162727210008170748822815415293507890852320733046100809748834172825790762441018033589952620148510568106987635330892667855860201758989207176495104 >>> (7 * n)) % 128

set_option maxRecDepth 8192 in
/-- Every table entry agrees with the mathematical totient formula. -/
theorem smallCosineDegree_check : ∀ n : Fin 232,
    smallCosineDegree n = fastTotient (2 * n) / 2 := by decide +kernel

/-- Use the verified table without exposing its encoding in later proofs. -/
theorem smallCosineDegree_eq (n : ℕ) (hn : n < 232) :
    smallCosineDegree n = (2 * n).totient / 2 := by
  simpa only [fastTotient_eq] using smallCosineDegree_check ⟨n, hn⟩

/-- The degree-compatible lists are cached as data to avoid repeatedly filtering. -/
def degreeCandidates : ℕ → List ℕ
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => [12, 15]
  | 5 => [11]
  | 6 => [13, 14, 18, 21]
  | 7 => []
  | 8 => [12, 15, 16, 17, 20, 24, 30]
  | 9 => [19, 27]
  | 10 => [11, 22, 25, 33]
  | 11 => [23]
  | 12 => [12, 13, 14, 15, 18, 21, 26, 28, 35, 36, 39, 42, 45]
  | 13 => []
  | 14 => [29]
  | 15 => [11, 31]
  | 16 => [12, 15, 16, 17, 20, 24, 30, 32, 34, 40, 48, 51, 60]
  | 17 => []
  | 18 => [13, 14, 18, 19, 21, 27, 37, 38, 54, 57, 63]
  | 19 => []
  | 20 => [11, 12, 15, 22, 25, 33, 41, 44, 50, 55, 66, 75]
  | 21 => [43, 49]
  | 22 => [23, 46, 69]
  | 23 => [47]
  | 24 => [12, 13, 14, 15, 16, 17, 18, 20, 21, 24, 26, 28, 30, 35, 36, 39, 42, 45, 52, 56, 65, 70, 72, 78, 84, 90, 105]
  | 25 => [11]
  | 26 => [53]
  | 27 => [19, 27, 81]
  | 28 => [12, 15, 29, 58, 87]
  | 29 => [59]
  | 30 => [11, 13, 14, 18, 21, 22, 25, 31, 33, 61, 62, 77, 93, 99]
  | 31 => []
  | 32 => [12, 15, 16, 17, 20, 24, 30, 32, 34, 40, 48, 51, 60, 64, 68, 80, 85, 96, 102, 120]
  | 33 => [23, 67]
  | 34 => []
  | 35 => [11, 71]
  | 36 => [12, 13, 14, 15, 18, 19, 21, 26, 27, 28, 35, 36, 37, 38, 39, 42, 45, 54, 57, 63, 73, 74, 76, 91, 95, 108, 111, 114, 117, 126, 135]
  | 37 => []
  | 38 => []
  | 39 => [79]
  | 40 => [11, 12, 15, 16, 17, 20, 22, 24, 25, 30, 33, 41, 44, 50, 55, 66, 75, 82, 88, 100, 110, 123, 132, 150, 165]
  | 41 => [83]
  | 42 => [13, 14, 18, 21, 29, 43, 49, 86, 98, 129, 147]
  | 43 => []
  | 44 => [12, 15, 23, 46, 69, 89, 92, 115, 138]
  | 45 => [11, 19, 27, 31]
  | 46 => [47, 94, 141]
  | 47 => []
  | 48 => [12, 13, 14, 15, 16, 17, 18, 20, 21, 24, 26, 28, 30, 32, 34, 35, 36, 39, 40, 42, 45, 48, 51, 52, 56, 60, 65, 70, 72, 78, 84, 90, 97, 104, 105, 112, 119, 130, 140, 144, 153, 156, 168, 180, 195, 210]
  | 49 => []
  | 50 => [11, 22, 25, 33, 101, 125]
  | 51 => [103]
  | 52 => [12, 15, 53, 106, 159]
  | 53 => [107]
  | 54 => [13, 14, 18, 19, 21, 27, 37, 38, 54, 57, 63, 81, 109, 133, 162, 171, 189]
  | 55 => [11, 23, 121]
  | 56 => [12, 15, 16, 17, 20, 24, 29, 30, 58, 87, 113, 116, 145, 174]
  | 57 => []
  | 58 => [59, 118, 177]
  | 59 => []
  | 60 => [11, 12, 13, 14, 15, 18, 21, 22, 25, 26, 28, 31, 33, 35, 36, 39, 41, 42, 44, 45, 50, 55, 61, 62, 66, 75, 77, 93, 99, 122, 124, 143, 154, 155, 175, 183, 186, 198, 225, 231]
  | 61 => []
  | 62 => []
  | 63 => [19, 27, 43, 49, 127]
  | _ => []

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
/-- Every cached list is checked against its defining degree condition. -/
theorem degreeCandidates_check : ∀ d : Fin 64, 0 < (d : ℕ) →
    degreeCandidates d = (List.range 232).filter (fun n => decide (11 ≤ n ∧ smallCosineDegree n ∣ (d : ℕ))) := by
  decide +kernel

end ArithmeticTriangles

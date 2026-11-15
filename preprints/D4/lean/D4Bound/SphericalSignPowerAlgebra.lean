import D4Bound.SphericalSignTensorPoly
set_option maxHeartbeats 0
set_option Elab.async false
namespace D4Bound.SphericalSign
open Bernstein

def addTensor (p q : Tensor) : Tensor := fun i j k => p i j k+q i j k
def scaleTensor (d : ℤ) (p : Tensor) : Tensor := fun i j k => d*p i j k
def constTensor (d : ℤ) : Tensor := fun i j k =>
  if i=0 then if j=0 then if k=0 then d else 0 else 0 else 0
def swapYZ (p : Tensor) : Tensor := fun i j k => p i k j
def cycleTensor (p : Tensor) : Tensor := fun i j k => p j k i
def cyclicTensor (p : Tensor) : Tensor := addTensor (addTensor p (swapYZ p)) (cycleTensor p)

lemma powerEv_add (p q : Tensor) (x y z : ℝ) :
    powerEv (addTensor p q) x y z=powerEv p x y z+powerEv q x y z := by
  simp only [powerEv,addTensor,Int.cast_add,add_mul,Finset.sum_add_distrib]
lemma powerEv_scale (d : ℤ) (p : Tensor) (x y z : ℝ) :
    powerEv (scaleTensor d p) x y z=(d:ℝ)*powerEv p x y z := by
  simp only [powerEv,scaleTensor,Int.cast_mul,Finset.mul_sum,mul_assoc]
lemma powerEv_const (d : ℤ) (x y z : ℝ) : powerEv (constTensor d) x y z=d := by
  simp [powerEv,constTensor]

lemma powerEv_swapYZ (p : Tensor) (x y z : ℝ) :
    powerEv (swapYZ p) x y z=powerEv p x z y := by
  unfold powerEv swapYZ
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma powerEv_cycle (p : Tensor) (x y z : ℝ) :
    powerEv (cycleTensor p) x y z=powerEv p y z x := by
  unfold powerEv cycleTensor
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma powerEv_cyclic (p : Tensor) (x y z : ℝ) :
    powerEv (cyclicTensor p) x y z=powerEv p x y z+powerEv p x z y+powerEv p y z x := by
  simp only [cyclicTensor,powerEv_add,powerEv_swapYZ,powerEv_cycle]

#print axioms powerEv_cyclic
end D4Bound.SphericalSign

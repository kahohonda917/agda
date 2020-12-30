module CPSt where

open import rplus
open import Data.Nat
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Empty
open import Data.Product
open import Function
open import Relation.Nullary
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality


    
--target type
data cpstyp : Set where
  Nat : cpstyp
  Bool : cpstyp
  _⇒_ : cpstyp → cpstyp → cpstyp
  ∙ : cpstyp



--target

mutual
  data cpsvalue[_]_ (var : cpstyp → Set) : cpstyp → Set where
    CPSVar : {τ₁ : cpstyp} → var τ₁ → cpsvalue[ var ] τ₁
    CPSNum : ℕ → cpsvalue[ var ] Nat
    CPSFun : {τ₁ τ₂ : cpstyp} → (var τ₂ → cpsterm[ var ] τ₁) →
             cpsvalue[ var ] (τ₂ ⇒ τ₁)

  data cpsterm[_]_ (var : cpstyp → Set) : cpstyp → Set where
    CPSVal    : {τ₁ : cpstyp} → cpsvalue[ var ] τ₁ →
                cpsterm[ var ] τ₁
    CPSTer    : {τ₁ : cpstyp} → var τ₁ → cpsterm[ var ] τ₁
    CPSApp    : {τ₁ τ₂ : cpstyp} → cpsterm[ var ] (τ₂ ⇒ τ₁) →
                cpsterm[ var ] τ₂ → cpsterm[ var ] τ₁
    CPSLet    : {τ₁ τ₂ : cpstyp} → cpsterm[ var ] τ₁ →
                (var τ₁ → cpsterm[ var ] τ₂) →
                cpsterm[ var ] τ₂
    CPSPlus   : cpsvalue[ var ] Nat →
                cpsvalue[ var ] Nat →
                cpsterm[ var ] Nat
    CPSId     : {μ : cpstyp} → cpsterm[ var ] μ
    CPSTrail  : {τ₁ τ₂ : cpstyp} → cpsterm[ var ] τ₁ →
                cpsterm[ var ] τ₂
    CPSIdk    : {τ₁ τ₂ τ₃ : cpstyp} → cpsvalue[ var ] τ₁ →
                cpsterm[ var ] τ₂ → cpsterm[ var ] τ₃
    CPSAppend : {τ₁ τ₃ : cpstyp} → cpsterm[ var ] τ₁ →
                cpsterm[ var ] τ₁ → cpsterm[ var ] τ₃
    CPSCons   : {τ₁ τ₂ τ₃ : cpstyp} → cpsterm[ var ] τ₁ →
                cpsterm[ var ] τ₂ → cpsterm[ var ] τ₃

--typ transform

mutual
  cpsT : typ → cpstyp
  cpsT Nat = Nat
  cpsT Tbool = Bool
  cpsT (τ₂ ⇒ τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β) =
       cpsT τ₂ ⇒ ((cpsT τ₁ ⇒ (cpsM μα ⇒ cpsT α)) ⇒ (cpsM μβ ⇒ cpsT β))

  cpsM : trail → cpstyp
  cpsM ∙ = ∙
  cpsM (_⇒_,_ τ τ' μ) = (cpsT τ ⇒ cpsM μ) ⇒ cpsT τ'


mutual
  cpsV : {τ₁ : typ} → {var : cpstyp → Set} →
       value[ var ∘ cpsT ] τ₁ → cpsvalue[ var ] (cpsT τ₁)
  cpsV (Var x) = CPSVar x
  cpsV (Num n) = CPSNum n
  cpsV (Fun e) = CPSFun (λ x → CPSVal (CPSFun (λ k' → CPSVal (CPSFun (λ t' →
                 cpsTerm (e x) (λ v t'' →
                 CPSApp (CPSApp (CPSTer k') (CPSVal v)) t'') (CPSTer t'))))))
       

  cpsTerm : {τ₁ α β : typ}{μα μβ : trail} → {var : cpstyp → Set} →
            term[ var ∘ cpsT ] τ₁ ⟨ μα ⟩ α ⟨ μβ ⟩ β →
            (cpsvalue[ var ] (cpsT τ₁) → cpsterm[ var ] (cpsM μα) → cpsterm[ var ] (cpsT α)) →
            cpsterm[ var ] (cpsM μβ) →
            cpsterm[ var ] (cpsT β)
  cpsTerm  (Val v) k t = k (cpsV v) t

  cpsTerm  (App e₁ e₂) k t = cpsTerm e₁ (λ v₁ t₁ → cpsTerm e₂
                             (λ v₂ t₂ → CPSApp (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                             (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t'' →
                             k (CPSVar v) (CPSVal (CPSVar t'')))))))) t₂) t₁) t
                           
  cpsTerm  (Plus e₁ e₂) k t = cpsTerm e₁ (λ v₁ t₁ → cpsTerm e₂
                              (λ v₂ t₂ → CPSLet (CPSPlus v₁ v₂) (λ v → k (CPSVar v) t₂)) t₁) t
                            
  cpsTerm  (Control x x₂ x₃ e) k t = CPSLet (CPSVal (CPSFun (λ v →
                                     CPSVal (CPSFun (λ k' → CPSVal (CPSFun (λ t' →
                                     CPSLet (CPSAppend t (CPSCons (CPSTer k') (CPSTer t')))
                                     (λ t'' → k (CPSVar v) (CPSTer t'')))))))))
                                     (λ x' → cpsTerm (e x') CPSIdk CPSId)
  
  cpsTerm  (Prompt x e) k t = CPSLet (cpsTerm e CPSIdk CPSId) λ v → k (CPSVar v) t

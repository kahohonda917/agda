module CPSt2 where

open import DSt2

open import Data.Nat using (ℕ; _+_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

--target type
data cpstyp : Set where
  Nat  : cpstyp
  Bool : cpstyp
  _⇛_  : cpstyp → cpstyp → cpstyp
  ∙    : cpstyp

--typ transform
mutual
  cpsT : typ → cpstyp
  cpsT Nat = Nat
  cpsT Tbool = Bool
  cpsT (τ₂ ⇒ τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β) =
       cpsT τ₂ ⇛ ((cpsT τ₁ ⇛ (cpsMs μs ⇛ cpsT α)) ⇛ (cpsM μβ ⇛ cpsT β))

  cpsM : trail → cpstyp
  cpsM ∙ = ∙
  cpsM (τ ⇒ τ' , μ) = cpsT τ ⇛ (cpsM μ ⇛ cpsT τ')

  cpsMs : {μα μβ : trail} → (μs : trails[ μβ ] μα) → cpstyp
  cpsMs {μα}μs = cpsM μα

--CPS項
mutual
  data cpsvalue[_]_ (var : cpstyp → Set) : cpstyp → Set where
    CPSVar    : {τ₁ : cpstyp} → var τ₁ → cpsvalue[ var ] τ₁
    CPSNum    : ℕ → cpsvalue[ var ] Nat
    CPSFun    : {τ₁ τ₂ : cpstyp} → (var τ₂ → cpsterm[ var ] τ₁) →
                cpsvalue[ var ] (τ₂ ⇛ τ₁)
    CPSId     : cpsvalue[ var ] ∙
    CPSAppend : {μ₁ μ₂ μ₃ : trail} → compatible μ₁ μ₂ μ₃ →
                cpsvalue[ var ] cpsM μ₁ →
                cpsvalue[ var ] cpsM μ₂ → cpsvalue[ var ] cpsM μ₃
    CPSCons   : {μ₀ μ₁ μ₂ : trail} → compatible μ₁ μ₂ μ₀ →
                cpsvalue[ var ] cpsM μ₁ →
                cpsvalue[ var ] cpsM μ₂ → cpsvalue[ var ] cpsM μ₀

  data cpsterm[_]_ (var : cpstyp → Set) : cpstyp → Set where
    CPSVal    : {τ₁ : cpstyp} → cpsvalue[ var ] τ₁ →
                cpsterm[ var ] τ₁
    CPSApp    : {τ₁ τ₂ : cpstyp} → cpsterm[ var ] (τ₂ ⇛ τ₁) →
                cpsterm[ var ] τ₂ → cpsterm[ var ] τ₁
    CPSLet    : {τ₁ τ₂ : cpstyp} → cpsterm[ var ] τ₁ →
                (var τ₁ → cpsterm[ var ] τ₂) →
                cpsterm[ var ] τ₂
    CPSPlus   : cpsterm[ var ] Nat →
                cpsterm[ var ] Nat →
                cpsterm[ var ] Nat
    CPSIdk    : {τ₁ τ₂ : typ} {μ : trail} → is-id-trail τ₁ τ₂ μ →
                cpsvalue[ var ] cpsT τ₁ →
                cpsvalue[ var ] cpsM μ → cpsterm[ var ] cpsT τ₂

mutual
  cpsV : {τ₁ : typ} → {var : cpstyp → Set} →
         value[ var ∘ cpsT ] τ₁ → cpsvalue[ var ] (cpsT τ₁)
  cpsV (Var x) = CPSVar x
  cpsV (Num n) = CPSNum n
  cpsV (Fun e) =
    CPSFun (λ x → CPSVal (CPSFun (λ k' → CPSVal (CPSFun (λ t' →
      cpsTerm (e x)
        (λ v t'' → CPSApp (CPSApp (CPSVal (CPSVar k')) (CPSVal v))
                          (CPSVal t''))
        (CPSVar t'))))))

  cpsTerm : {τ₁ α β : typ} {μα μβ : trail} {μs : trails[ μβ ] μα} →
            {var : cpstyp → Set} →
            term[ var ∘ cpsT ] τ₁ ⟨ μs ⟩ α ⟨ μβ ⟩ β →
            (cpsvalue[ var ] (cpsT τ₁) → cpsvalue[ var ] (cpsMs μs) →
             cpsterm[ var ] (cpsT α)) →
            cpsvalue[ var ] (cpsM μβ) →
            cpsterm[ var ] (cpsT β)
  cpsTerm  (Val v) k t = k (cpsV v) t

  cpsTerm  (App e₁ e₂) k t =
    cpsTerm e₁ (λ v₁ t₁ →
      cpsTerm e₂ (λ v₂ t₂ →
        CPSApp (CPSApp (CPSApp (CPSVal v₁) (CPSVal v₂))
                       (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t'' →
                         k (CPSVar v) (CPSVar t'')))))))
               (CPSVal t₂)) t₁) t

  cpsTerm  (Plus e₁ e₂) k t =
    cpsTerm e₁ (λ v₁ t₁ →
      cpsTerm e₂ (λ v₂ t₂ →
        CPSLet (CPSPlus (CPSVal v₁) (CPSVal v₂))
               (λ v → k (CPSVar v) t₂)) t₁) t

  cpsTerm  (Control x x₂ x₃ e) k t =
    CPSLet (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ k' →
             CPSVal (CPSFun (λ t' →
               CPSLet (CPSVal (CPSAppend x₃ t
                                         (CPSCons x₂ (CPSVar k') (CPSVar t'))))
                      (λ t'' → k (CPSVar v) (CPSVar t'')))))))))
           (λ x' → cpsTerm (e x') (CPSIdk x) (CPSId))

  cpsTerm  (Prompt x e) k t =
    CPSLet (cpsTerm e (CPSIdk x) (CPSId))
           (λ v → k (CPSVar v) t)

--subst

mutual
  data cpsSubstVal {var : cpstyp → Set} : {τ₁ τ₂ : cpstyp} →
                   (var τ₁ → cpsvalue[ var ] τ₂) →
                   cpsvalue[ var ] τ₁ →
                   cpsvalue[ var ] τ₂ → Set where

    sVar= : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} →
            cpsSubstVal (λ x → CPSVar x) v v

    sVar≠ : {τ₁ τ₂ : cpstyp} {v : cpsvalue[ var ] τ₂} {x : var τ₁} →
            cpsSubstVal (λ _ → CPSVar x) v (CPSVar x)

    sNum  : {τ₁ : cpstyp} {v : cpsvalue[ var ] τ₁} {n : ℕ} →
            cpsSubstVal (λ _ → CPSNum n) v (CPSNum n)

    sFun  : {τ τ₁ τ₂ : cpstyp} →
            {e₁ : var τ → var τ₁ → cpsterm[ var ] τ₂} →
            {v : cpsvalue[ var ] τ} →
            {e₁′ : var τ₁ → cpsterm[ var ] τ₂} →
            ((x : var τ₁) → cpsSubst (λ y → (e₁ y) x) v (e₁′ x)) →
            cpsSubstVal (λ y → CPSFun (e₁ y)) v (CPSFun e₁′)

    sId  : {τ : cpstyp} → {v : cpsvalue[ var ] τ} →
           cpsSubstVal (λ y → CPSId) v (CPSId)

    sTra : {τ τ₁ : cpstyp} →
           {e : var τ → cpsvalue[ var ] τ₁} →
           {v : cpsvalue[ var ] τ} →
           {e′ : cpsvalue[ var ] τ₁} →
           cpsSubstVal e v e′ →
           cpsSubstVal (λ y → (e y)) v e′

    sApd : {τ : cpstyp} {μ₁ μ₂ μ₃ : trail} →
           {x : compatible μ₁ μ₂ μ₃} →
           {e₁ : var τ → cpsvalue[ var ] cpsM μ₁} →
           {e₂ : var τ → cpsvalue[ var ] cpsM μ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsvalue[ var ] cpsM μ₁} →
           {e₂′ : cpsvalue[ var ] cpsM μ₂} →
           cpsSubstVal e₁ v e₁′ → cpsSubstVal e₂ v e₂′ →
           cpsSubstVal (λ y → CPSAppend x (e₁ y) (e₂ y)) v
                       (CPSAppend x e₁′ e₂′)

    sCon : {τ : cpstyp} {μ₀ μ₁ μ₂ : trail} →
           {x : compatible μ₁ μ₂ μ₀} →
           {e₁ : var τ → cpsvalue[ var ] cpsM μ₁} →
           {e₂ : var τ → cpsvalue[ var ] cpsM μ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsvalue[ var ] cpsM μ₁} →
           {e₂′ : cpsvalue[ var ] cpsM μ₂} →
           cpsSubstVal e₁ v e₁′ → cpsSubstVal e₂ v e₂′ →
           cpsSubstVal (λ y → CPSCons x (e₁ y) (e₂ y)) v (CPSCons x e₁′ e₂′)

  data cpsSubst {var : cpstyp → Set} : {τ₁ τ₂ : cpstyp} →
                (var τ₁ → cpsterm[ var ] τ₂) →
                cpsvalue[ var ] τ₁ →
                cpsterm[ var ] τ₂ → Set where

    sVal : {τ τ₁ : cpstyp} →
           {v₁ : var τ → cpsvalue[ var ] τ₁} →
           {v : cpsvalue[ var ] τ} →
           {v₁′ : cpsvalue[ var ] τ₁} →
           cpsSubstVal v₁ v v₁′ →
           cpsSubst (λ y → CPSVal (v₁ y)) v (CPSVal v₁′)

    sApp : {τ τ₁ τ₂ : cpstyp} →
           {e₁ : var τ → cpsterm[ var ] (τ₂ ⇛ τ₁)} →
           {e₂ : var τ → cpsterm[ var ] τ₂} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] (τ₂ ⇛ τ₁)} →
           {e₂′ : cpsterm[ var ] τ₂} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSApp (e₁ y) (e₂ y)) v (CPSApp e₁′ e₂′)

    sLet : {τ τ₁ τ₂ : cpstyp} →
           {e₁ : var τ₁ → cpsterm[ var ] τ} →
           {e₂ : var τ₁ → var τ → cpsterm[ var ] τ₂} →
           {v : cpsvalue[ var ] τ₁} →
           {e₁′ : cpsterm[ var ] τ} →
           {e₂′ : var τ → cpsterm[ var ] τ₂} →
           ((x : var τ) → cpsSubst (λ y → (e₂ y) x) v (e₂′ x)) →
           ((x : var τ) → cpsSubst (λ y → e₁ y) v e₁′) →
           cpsSubst (λ y → CPSLet (e₁ y) (e₂ y)) v (CPSLet e₁′ e₂′)

    sPlu : {τ : cpstyp} →
           {e₁ : var τ → cpsterm[ var ] Nat} →
           {e₂ : var τ → cpsterm[ var ] Nat} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsterm[ var ] Nat} →
           {e₂′ : cpsterm[ var ] Nat} →
           cpsSubst e₁ v e₁′ → cpsSubst e₂ v e₂′ →
           cpsSubst (λ y → CPSPlus (e₁ y) (e₂ y)) v (CPSPlus e₁′ e₂′)

    sIdk : {τ : cpstyp} {τ₁ τ₂ : typ} {μ : trail} →
           {x : is-id-trail τ₁ τ₂ μ} →
           {e₁ : var τ → cpsvalue[ var ] cpsT τ₁} →
           {e₂ : var τ → cpsvalue[ var ] cpsM μ} →
           {v : cpsvalue[ var ] τ} →
           {e₁′ : cpsvalue[ var ] cpsT τ₁} →
           {e₂′ : cpsvalue[ var ] cpsM μ} →
           cpsSubstVal e₁ v e₁′ → cpsSubstVal e₂ v e₂′ →
           cpsSubst (λ y → CPSIdk x (e₁ y) (e₂ y)) v (CPSIdk x e₁′ e₂′)

data cpsreduce {var : cpstyp → Set} : {τ₁ : cpstyp} →
              cpsterm[ var ] τ₁ →
              cpsterm[ var ] τ₁ → Set where

  rBeta    : {τ τ₁ : cpstyp} →
             {e₁ : var τ → cpsterm[ var ] τ₁} →
             {v : cpsvalue[ var ] τ} →
             {e₁′ : cpsterm[ var ] τ₁} →
             cpsSubst e₁ v e₁′ →
             cpsreduce (CPSApp (CPSVal (CPSFun e₁)) (CPSVal v)) e₁′

  rPlus    : {n₁ n₂ : ℕ} →
             cpsreduce (CPSPlus (CPSVal (CPSNum n₁)) (CPSVal (CPSNum n₂)))
             (CPSVal (CPSNum (n₁ + n₂)))

  rFun     : {τ₁ τ₂ : cpstyp} →
             {e₁ e₂ : var τ₂ → cpsterm[ var ] τ₁} →
             ((x : var τ₂) → cpsreduce (e₁ x) (e₂ x)) →
             cpsreduce (CPSVal (CPSFun (λ x → e₁ x)))
                       (CPSVal (CPSFun (λ x → e₂ x)))

  rApp₁    : {τ₁ τ₂ : cpstyp} →
             {e₁ e₁′ : cpsterm[ var ] (τ₂ ⇛ τ₁)} →
             {e₂ : cpsterm[ var ] τ₂} →
             cpsreduce e₁ e₁′ →
             cpsreduce (CPSApp e₁ e₂) (CPSApp e₁′ e₂)

  rApp₂    : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] (τ₂ ⇛ τ₁)} →
             {e₂ e₂′ : cpsterm[ var ] τ₂} →
             cpsreduce e₂ e₂′ →
             cpsreduce (CPSApp e₁ e₂) (CPSApp e₁ e₂′)

  rCon₁    : {τ₁ τ₂ : typ} {μ₀ μ₁ μ₂ : trail} →
             {x : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀} →
             {v₁ v₁′ : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {v₂ : cpsvalue[ var ] cpsM μ₂} →
             cpsreduce (CPSVal v₁) (CPSVal v₁′) →
             cpsreduce (CPSVal (CPSCons x v₁ v₂)) (CPSVal (CPSCons x v₁′ v₂))

  rCon₂    : {τ₁ τ₂ : typ} {μ₀ μ₁ μ₂ : trail} →
             {x : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₀}  →
             {v₁ : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {v₂ v₂′ : cpsvalue[ var ] cpsM μ₂} →
             cpsreduce (CPSVal v₂) (CPSVal v₂′) →
             cpsreduce (CPSVal (CPSCons x v₁ v₂)) (CPSVal (CPSCons x v₁ v₂′))

  rLet     : {τ τ₁ : cpstyp} →
             {v : cpsvalue[ var ] τ} →
             {e₁ : var τ → cpsterm[ var ] τ₁} →
             {e₁′ : cpsterm[ var ] τ₁} →
             cpsSubst e₁ v e₁′ →
             cpsreduce (CPSLet (CPSVal v) e₁) e₁′

  rLet₁    : {τ₁ τ₂ : cpstyp} →
             {e₁ e₁′ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] τ₂} →
             cpsreduce e₁ e₁′ →
             cpsreduce (CPSLet e₁ e₂) (CPSLet e₁′ e₂)

  rLet₂    : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] τ₁} →
             {e₂ e₂′ : var τ₁ → cpsterm[ var ] τ₂} →
             ((x : var τ₁) → cpsreduce (e₂ x) (e₂′ x)) →
             cpsreduce (CPSLet e₁ e₂) (CPSLet e₁ e₂′)

  rLet₃    : {τ₁ τ₂ τ₃ : cpstyp} →
             {e₁ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] (τ₂ ⇛ τ₃)} →
             {e₃ : cpsterm[ var ] τ₂} →
             cpsreduce (CPSApp (CPSLet e₁ (λ x → e₂ x)) e₃)
                       (CPSLet e₁ (λ x → CPSApp (e₂ x) e₃))

  rLetApp  : {τ₁ τ₂ : cpstyp} →
             {e₁ : cpsterm[ var ] τ₁} →
             {e₂ : var τ₁ → cpsterm[ var ] τ₂} →
             cpsreduce (CPSLet e₁ (λ x → e₂ x))
                       (CPSApp (CPSVal (CPSFun (λ x → e₂ x))) e₁)

  rAppend₁ : {μ₁ μ₂ μ₃ : trail} →
             {x : compatible μ₁ μ₂ μ₃} →
             {e₁ e₁′ : cpsvalue[ var ] cpsM μ₁} →
             {e₂ : cpsvalue[ var ] cpsM μ₂} →
             cpsreduce (CPSVal e₁) (CPSVal e₁′) →
             cpsreduce (CPSVal (CPSAppend x e₁ e₂))
                       (CPSVal (CPSAppend x e₁′ e₂))

--idk,cons,appendの簡約規則
  rApdid   : {μ₂ : trail} →
             {v : cpsvalue[ var ] cpsM μ₂} →
             cpsreduce (CPSVal (CPSAppend refl CPSId v)) (CPSVal v)

  rApdt    : {τ₁ τ₂ : typ} {μ₁ μ₂ μ₃ : trail} →
             {x : compatible (τ₁ ⇒ τ₂ , μ₁) μ₂ μ₃} →
             {k : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {t : cpsvalue[ var ] cpsM μ₂} →
             cpsreduce (CPSVal (CPSAppend x k t))
                       (CPSVal (CPSCons x k t))

  rConsid  : {τ₁ τ₂ : typ} {μ₁ : trail} →
             -- {x : compatible (τ₁ ⇒ τ₂ , μ₁) ∙ μ₀} →
             {v₁ : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             cpsreduce (CPSVal (CPSCons refl v₁ CPSId)) (CPSVal v₁)

  rConsid₂  : {τ₁ τ₂ : typ} {μ₁ : trail} →
             -- {x : compatible (τ₁ ⇒ τ₂ , μ₁) ∙ μ₀} →
             {v₁ : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {id : cpsvalue[ var ] ∙} →
             cpsreduce (CPSVal (CPSCons refl v₁ id)) (CPSVal v₁)

  rConst   : {τ₁ τ₁' τ₂ τ₂' : typ} {μ₁ μ₁' μ₂' : trail} →
             {x : compatible (τ₁ ⇒ τ₂ , μ₁) (τ₁' ⇒ τ₂' , μ₁')
                             (τ₁ ⇒ τ₂ , μ₂') } →
             {x₂ : compatible (τ₁' ⇒ τ₂' , μ₁') μ₂' μ₁}
             {k : cpsvalue[ var ] (cpsT τ₁ ⇛ (cpsM μ₁ ⇛ cpsT τ₂))} →
             {k′ : cpsvalue[ var ] (cpsT τ₁' ⇛ (cpsM μ₁' ⇛ cpsT τ₂'))} →
             cpsreduce
               (CPSVal (CPSCons x k k′))
               (CPSVal (CPSFun (λ v → CPSVal (CPSFun (λ t' →
                 CPSApp (CPSApp (CPSVal k) (CPSVal (CPSVar v)))
                        (CPSVal (CPSCons x₂ k′ (CPSVar t'))))))))

  rIdkid   : {τ₁ : typ} →
             {v : cpsvalue[ var ] cpsT τ₁} →
             cpsreduce (CPSIdk refl v (CPSId)) (CPSVal v)

  rIdkt    : {τ₁ τ₂ : typ} →
             {x : is-id-trail τ₁ τ₂ (τ₁ ⇒ τ₂ , ∙)} →
             {v : cpsvalue[ var ] cpsT τ₁} →
             {k : cpsvalue[ var ] (cpsT τ₁ ⇛ (∙ ⇛ cpsT τ₂))} →
             cpsreduce (CPSIdk x v (k))
                       (CPSApp (CPSApp (CPSVal k) (CPSVal v)) (CPSVal CPSId))

  r*Id     : {τ : cpstyp} →
             {e : cpsterm[ var ] τ} →
             cpsreduce e e

  r*Trans  : {τ : cpstyp} →
             (e₁ e₂ e₃ : cpsterm[ var ] τ) →
             cpsreduce e₁ e₂ →
             cpsreduce e₂ e₃ →
             cpsreduce e₁ e₃

  r*Trans′  : {τ : cpstyp} →
             (e₁ e₂ e₃ : cpsterm[ var ] τ) →
             cpsreduce e₂ e₁ →
             cpsreduce e₂ e₃ →
             cpsreduce e₁ e₃

-- equational reasoning
infix  3 _∎
infixr 2 _⟶⟨_⟩_ _⟵⟨_⟩_ _≡⟨_⟩_
infix  1 begin_

begin_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
         {e₁ e₂ : cpsterm[ var ] τ₁ } → cpsreduce e₁ e₂ → cpsreduce e₁ e₂
begin_ red = red

_⟶⟨_⟩_ : {var : cpstyp → Set} → {τ₁ : cpstyp} →
           (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
           cpsreduce e₁ e₂ → cpsreduce e₂ e₃ → cpsreduce e₁ e₃
_⟶⟨_⟩_ e₁ {e₂} {e₃} e₁-red-e₂ e₂-red*-e₃ =
  r*Trans e₁ e₂ e₃ e₁-red-e₂ e₂-red*-e₃

_⟵⟨_⟩_ : {var : cpstyp → Set} {τ₁ : cpstyp} →
          (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) →
          cpsreduce e₂ e₁ → cpsreduce e₂ e₃ → cpsreduce e₁ e₃
_⟵⟨_⟩_ e₁ {e₂} {e₃} e₂-eq-e₁ e₂-eq-e₃ = r*Trans′ e₁ e₂ e₃ e₂-eq-e₁ e₂-eq-e₃

_≡⟨_⟩_ : {var : cpstyp → Set} → {τ₁ : cpstyp} →
         (e₁ {e₂ e₃} : cpsterm[ var ] τ₁) → e₁ ≡ e₂ → cpsreduce e₂ e₃ →
         cpsreduce e₁ e₃
_≡⟨_⟩_ e₁ {e₂} {e₃} refl e₂-red*-e₃ = e₂-red*-e₃

_∎ : {var : cpstyp → Set} {τ₁ : cpstyp} →
     (e : cpsterm[ var ] τ₁) → cpsreduce e e
_∎ e = r*Id

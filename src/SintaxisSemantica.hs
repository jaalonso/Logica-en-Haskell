-- SintaxisSemanticaProp.hs
-- Lógica proposicional: Sintaxis y semántica
-- José A. Alonso Jiménez https://jaalonso.github.com
-- =====================================================================

module SintaxisSemantica where

-- ---------------------------------------------------------------------
-- § Librerías auxiliares                                             --
-- ---------------------------------------------------------------------

import Data.List

-- ---------------------------------------------------------------------
-- § Gramática de fórmulas prosicionales                              --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 1: Definir los siguientes tipos de datos:
-- + SimboloProposicional para representar los símbolos de proposiciones
-- + Prop para representar las fórmulas proposicionales usando los
--   constructores Atom, Neg, Conj, Disj, Impl y Equi para las fórmulas
--   atómicas, negaciones, conjunciones, implicaciones y equivalencias,
--   respectivamente.
-- ---------------------------------------------------------------------

type SimboloProposicional = String

data Prop = Atom SimboloProposicional
          | Neg Prop
          | Conj Prop Prop
          | Disj Prop Prop
          | Impl Prop Prop
          | Equi Prop Prop
  deriving (Eq, Ord)

instance Show Prop where
  show (Atom f)   = f
  show (Neg f)    = "no " ++ show f
  show (Conj f g) = "(" ++ show f ++ " /\\ " ++ show g ++ ")"
  show (Disj f g) = "(" ++ show f ++ " \\/ " ++ show g ++ ")"
  show (Impl f g) = "(" ++ show f ++ " --> " ++ show g ++ ")"
  show (Equi f g) = "(" ++ show f ++ " <--> " ++ show g ++ ")"

-- ---------------------------------------------------------------------
-- Ejercicio 2: Definir las siguientes fórmulas proposicionales
-- atómicas: p, p1, p2, q, r, s, t y u.
-- ---------------------------------------------------------------------

p, p1, p2, q, r, s, t, u :: Prop
p  = Atom "p"
p1 = Atom "p1"
p2 = Atom "p2"
q  = Atom "q"
r  = Atom "r"
s  = Atom "s"
t  = Atom "t"
u  = Atom "u"

-- ---------------------------------------------------------------------
-- Ejercicio 3: Definir la función
--    no :: Prop -> Prop
-- tal que (no f) es la negación de f.
-- ---------------------------------------------------------------------

no :: Prop -> Prop
no = Neg

-- ---------------------------------------------------------------------
-- Ejercicio 4: Definir los siguientes operadores
--    (/\), (\/), (-->), (<-->) :: Prop -> Prop -> Prop
-- tales que
--    f /\ g      es la conjunción de f y g
--    f \/ g      es la disyunción de f y g
--    f --> g     es la implicación de f a g
--    f <--> g    es la equivalencia entre f y g
-- ---------------------------------------------------------------------

infixr 5 \/
infixr 4 /\
infixr 3 -->
infixr 2 <-->

(/\), (\/), (-->), (<-->) :: Prop -> Prop -> Prop
(/\)   = Conj
(\/)   = Disj
(-->)  = Impl
(<-->) = Equi

-- ---------------------------------------------------------------------
-- § Símbolos proposicionales de una fórmula                          --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 5: Definir la función
--    simbolosPropForm :: Prop -> [Prop]
-- tal que (simbolosPropForm f) es el conjunto formado por todos los
-- símbolos proposicionales que aparecen en f. Por ejemplo,
--    simbolosPropForm (p /\ q --> p)  == [p,q]
-- ---------------------------------------------------------------------

simbolosPropForm :: Prop -> [Prop]
simbolosPropForm (Atom f)   = [Atom f]
simbolosPropForm (Neg f)    = simbolosPropForm f
simbolosPropForm (Conj f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Disj f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Impl f g) = simbolosPropForm f `union` simbolosPropForm g
simbolosPropForm (Equi f g) = simbolosPropForm f `union` simbolosPropForm g

-- ---------------------------------------------------------------------
-- § Interpretaciones                                                 --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 6: Definir el tipo de datos Interpretacion para
-- representar las interpretaciones como listas de fórmulas atómicas.
-- ---------------------------------------------------------------------

type Interpretacion = [Prop]

-- ---------------------------------------------------------------------
-- § Significado de una fórmula en una interpretación                 --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 7: Definir la función
--    significado :: Prop -> Interpretacion -> Bool
-- tal que (significado f i) es el significado de f en i. Por ejemplo,
--    significado ((p \/ q) /\ ((no q) \/ r)) [r]    ==  False
--    significado ((p \/ q) /\ ((no q) \/ r)) [p,r]  ==  True
-- ---------------------------------------------------------------------

significado :: Prop -> Interpretacion -> Bool
significado (Atom f)   i = Atom f `elem` i
significado (Neg f)    i = not (significado f i)
significado (Conj f g) i = significado f i && significado g i
significado (Disj f g) i = significado f i || significado g i
significado (Impl f g) i = significado (Disj (Neg f) g) i
significado (Equi f g) i = significado (Conj (Impl f g) (Impl g f)) i

-- ---------------------------------------------------------------------
-- § Interpretaciones de una fórmula                                  --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 8: Definir la función
--    subconjuntos :: [a] -> [[a]]
-- tal que (subconjuntos x) es la lista de los subconjuntos de x. Por
-- ejmplo,
--    subconjuntos "abc"  ==  ["abc","ab","ac","a","bc","b","c",""]
-- ---------------------------------------------------------------------

subconjuntos :: [a] -> [[a]]
subconjuntos []     = [[]]
subconjuntos (x:xs) = [x:ys | ys <- xss] ++ xss
  where xss = subconjuntos xs

-- ---------------------------------------------------------------------
-- Ejercicio 9: Definir la función
--    interpretacionesForm :: Prop -> [Interpretacion]
-- tal que (interpretacionesForm f) es la lista de todas las
-- interpretaciones de f. Por ejemplo,
--    interpretacionesForm (p /\ q --> p)  ==  [[p,q],[p],[q],[]]
-- ---------------------------------------------------------------------

interpretacionesForm :: Prop -> [Interpretacion]
interpretacionesForm = subconjuntos . simbolosPropForm

-- ---------------------------------------------------------------------
-- § Modelos de fórmulas                                              --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 10: Definir la función
--    esModeloFormula :: Interpretacion -> Prop -> Bool
-- tal que (esModeloFormula i f) se verifica si i es un modelo de f. Por
-- ejemplo,
--    esModeloFormula [r]   ((p \/ q) /\ ((no q) \/ r))    ==  False
--    esModeloFormula [p,r] ((p \/ q) /\ ((no q) \/ r))    ==  True
-- ---------------------------------------------------------------------

esModeloFormula :: Interpretacion -> Prop -> Bool
esModeloFormula i f = significado f i

-- ---------------------------------------------------------------------
-- Ejercicio 11: Definir la función
--    modelosFormula :: Prop -> [Interpretacion]
-- tal que (modelosFormula f) es la lista de todas las interpretaciones
-- de f que son modelo de F. Por ejemplo,
--    modelosFormula ((p \/ q) /\ ((no q) \/ r))
--    == [[p,q,r],[p,r],[p],[q,r]]
-- ---------------------------------------------------------------------

modelosFormula :: Prop -> [Interpretacion]
modelosFormula f =
  [i | i <- interpretacionesForm f,
       esModeloFormula i f]

-- ---------------------------------------------------------------------
-- § Fórmulas válidas, satisfacibles e insatisfacibles                --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 12: Definir la función
--    esValida :: Prop -> Bool
-- tal que (esValida f) se verifica si f es válida. Por ejemplo,
--    esValida (p --> p)                 ==  True
--    esValida (p --> q)                 ==  False
--    esValida ((p --> q) \/ (q --> p))  ==  True
-- ---------------------------------------------------------------------

esValida :: Prop -> Bool
esValida f =
  modelosFormula f == interpretacionesForm f

-- ---------------------------------------------------------------------
-- Ejercicio 13: Definir la función
--    esInsatisfacible :: Prop -> Bool
-- tal que (esInsatisfacible f) se verifica si f es insatisfacible. Por
-- ejemplo,
--    esInsatisfacible (p /\ (no p))             ==  True
--    esInsatisfacible ((p --> q) /\ (q --> r))  ==  False
-- ---------------------------------------------------------------------

esInsatisfacible :: Prop -> Bool
esInsatisfacible =
  null . modelosFormula

-- ---------------------------------------------------------------------
-- Ejercicio 14: Definir la función
--    esSatisfacible :: Prop -> Bool
-- tal que (esSatisfacible f) se verifica si f es satisfacible. Por
-- ejemplo,
--    esSatisfacible (p /\ (no p))             ==  False
--    esSatisfacible ((p --> q) /\ (q --> r))  ==  True
-- ---------------------------------------------------------------------

esSatisfacible :: Prop -> Bool
esSatisfacible =
  not . null . modelosFormula

-- ---------------------------------------------------------------------
-- § Símbolos proposicionales de un conjunto de fórmulas              --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 15: Definir la función
--    unionGeneral :: Eq a => [[a]] -> [a]
-- tal que (unionGeneral x) es la unión de los conjuntos de la lista de
-- conjuntos x. Por ejemplo,
--    unionGeneral []                 ==  []
--    unionGeneral [[1]]              ==  [1]
--    unionGeneral [[1],[1,2],[2,3]]  ==  [1,2,3]
-- ---------------------------------------------------------------------

unionGeneral :: Eq a => [[a]] -> [a]
unionGeneral = foldr union []

-- ---------------------------------------------------------------------
-- Ejercicio 16: Definir la función
--    simbolosPropConj :: [Prop] -> [Prop]
-- tal que (simbolosPropConj fs) es el conjunto de los símbolos
-- proposiciones de fs. Por ejemplo,
--    simbolosPropConj [p /\ q --> r, p --> s]  ==  [p,q,r,s]
-- ---------------------------------------------------------------------

simbolosPropConj :: [Prop] -> [Prop]
simbolosPropConj fs =
  unionGeneral [simbolosPropForm f | f <- fs]

-- ---------------------------------------------------------------------
-- § Interpretaciones de un conjunto de fórmulas                      --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 17: Definir la función
--    interpretacionesConjunto :: [Prop] -> [Interpretacion]
-- tal que (interpretacionesConjunto fs) es la lista de las
-- interpretaciones de fs. Por ejemplo,
--    interpretacionesConjunto [p --> q, q --> r]
--    == [[p,q,r],[p,q],[p,r],[p],[q,r],[q],[r],[]]
-- ---------------------------------------------------------------------

interpretacionesConjunto :: [Prop] -> [Interpretacion]
interpretacionesConjunto =
  subconjuntos . simbolosPropConj

-- ---------------------------------------------------------------------
-- § Modelos de conjuntos de fórmulas                                 --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 18: Definir la función
--    esModeloConjunto :: Interpretacion -> [Prop] -> Bool
-- tal que (esModeloConjunto i fs) se verifica si i es modelo de fs. Por
-- ejemplo,
--    esModeloConjunto [p,r] [(p \/ q) /\ ((no q) \/ r), q --> r]
--    == True
--    esModeloConjunto [p,r] [(p \/ q) /\ ((no q) \/ r), r --> q]
--    == False
-- ---------------------------------------------------------------------

esModeloConjunto :: Interpretacion -> [Prop] -> Bool
esModeloConjunto i fs =
  and [esModeloFormula i f | f <- fs]

-- ---------------------------------------------------------------------
-- Ejercicio 19: Definir la función
--    modelosConjunto :: [Prop] -> [Interpretacion]
-- tal que (modelosConjunto fs) es la lista de modelos del conjunto
-- s. Por ejemplo,
--    modelosConjunto [(p \/ q) /\ ((no q) \/ r), q --> r]
--    == [[p,q,r],[p,r],[p],[q,r]]
--    modelosConjunto [(p \/ q) /\ ((no q) \/ r), r --> q]
--    == [[p,q,r],[p],[q,r]]
-- ---------------------------------------------------------------------

modelosConjunto :: [Prop] -> [Interpretacion]
modelosConjunto fs =
  [i | i <- interpretacionesConjunto fs,
       esModeloConjunto i fs]

-- ---------------------------------------------------------------------
-- § Conjuntos consistentes e inconsistentes de fórmulas              --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 20: Definir la función
--    esConsistente :: [Prop] -> Bool
-- tal que (esConsistente fs) se verifica si fs es consistente. Por
-- ejemplo,
--    esConsistente [(p \/ q) /\ ((no q) \/ r), p --> r]
--    == True
--    esConsistente [(p \/ q) /\ ((no q) \/ r), p --> r, no r]
--    == False
-- ---------------------------------------------------------------------

esConsistente :: [Prop] -> Bool
esConsistente =
  not . null . modelosConjunto

-- ---------------------------------------------------------------------
-- Ejercicio 21: Definir la función
--    esInconsistente :: [Prop] -> Bool
-- tal que (esInconsistente fs) se verifica si fs es inconsistente. Por
-- ejemplo,
--    esInconsistente [(p \/ q) /\ ((no q) \/ r), p --> r]
--    == False
--    esInconsistente [(p \/ q) /\ ((no q) \/ r), p --> r, no r]
--    == True
-- ---------------------------------------------------------------------

esInconsistente :: [Prop] -> Bool
esInconsistente =
  null . modelosConjunto

-- ---------------------------------------------------------------------
-- § Consecuencia lógica                                              --
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 22: Definir la función
--    esConsecuencia :: [Prop] -> Prop -> Bool
-- tal que (esConsecuencia fs f) se verifica si f es consecuencia de
-- fs. Por ejemplo,
--    esConsecuencia [p --> q, q --> r] (p --> r)  ==  True
--    esConsecuencia [p] (p /\ q)                  ==  False
-- ---------------------------------------------------------------------

esConsecuencia :: [Prop] -> Prop -> Bool
esConsecuencia fs f =
  null [i | i <- interpretacionesConjunto (f:fs),
            esModeloConjunto i fs,
            not (esModeloFormula i f)]

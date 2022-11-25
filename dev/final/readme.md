# dépendances

Voici les dépendnances entre les fichiers du projet.

`X : Y Z` := `X` dépend de `Y` et de `Z` 

```
ordreNat 
modulo : ordreNat
fonctions
produitCartesien : fonctions
vecteurs :  fonctions produitCartesien modulo
frontend : fonctions vecteurs modulo String alphabets
backend : fonctions produitCartesien vecteurs modulo String.
```

# compilation

Une manière simple de gérer les dépendnaces est d'utiliser un fichier de
configuration et d'engendrer un "makefile".

- à partir du fichier `_CoqProject`, à produire initialement puis à
  enrichir avec les nouveux fichiers
- génération du `makefile` : `coq_makefile -f _CoqProject -o makefile`
- compilation après modificatin d'un fichier : `make`


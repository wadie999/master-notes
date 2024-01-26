#Projet TSP Solver

Ce projet propose deux approches pour résoudre le problème du voyageur de commerce (TSP) : une métaheuristique en Python et l'utilisation de SCIP avec le langage ZIMPL.

## Métaheuristique en Python

### Fichiers Importants
Le projet contient 3 fichiers importants :
####1. `salesman.py` (Classes City et TSPSolver)
 Pour compiler et exécuter ce fichier, assurez-vous d'avoir les 4 fichiers texte (`tsp-xx.txt`) dans le même répertoire.


###### Classe `City`

La classe `City` représente une ville dans le problème TSP. Elle a les attributs suivants :
- `city_id`: L'identifiant de la ville.
- `x`: La coordonnée x de la ville.
- `y`: La coordonnée y de la ville.

La méthode `distance_to` permet de calculer la distance entre deux villes en utilisant la distance euclidienne.

###### Classe `TSPSolver`

La classe `TSPSolver` est le cœur du solveur TSP. Elle prend en charge la résolution du problème en utilisant différentes méthodes.
#### Exécution
1. Ouvrez un terminal.
2. Exécutez le script Python en utilisant l'une des commandes suivantes :
   - Pour Python 3 : `python3 salesman.py`
   - Pour Python : `python salesman.py`
3. L'interface du terminal vous demandera de choisir le fichier de test à utiliser, le type de voisinage, et si vous souhaitez utiliser une liste tabou, vous devrez également saisir sa taille.
4. La métaheuristique se lancera et fournira une première solution.
5. Le programme vous demandera ensuite si vous souhaitez exécuter une recherche de montée de colline avec redémarrage.
####2. `salesman-animated.py` (Animation du Solveur)

Le fichier `salesman-animated.py` est une extension du projet qui ajoute une fonctionnalité d'animation pour visualiser le processus de résolution du problème du voyageur de commerce (TSP). Pour exécuter ce fichier, utilisez la commande suivante :
#### Exécution
1. `python salesman-animated.py <nom-fichier>`

####3. `salesman-discussion.ipynb` (Notebook)

Ce notebook regroupe différents tests et comparaisons des méthodes heuristiques en utilisant les différentes approches de voisinage disponibles.


## SCIP avec Langage ZIMPL

### Fichier Important
Assurez-vous d'avoir le fichier `tsp_solver.zpl` dans le même répertoire que les fichiers texte de test.

### Exécution
1. Ouvrez un terminal.
2. Exécutez les commandes suivantes pour utiliser SCIP :
   - Lancez SCIP : `scip`
   - Dans SCIP, lisez le fichier de modèle : `read tsp_solver.zpl`
   - Optimisez le problème : `optimize`
   - Affichez la solution : `display solution`

### Changement du Fichier de Test
Si vous souhaitez changer le fichier de test, suivez ces étapes simples :
1. Modifiez les trois premières lignes du fichier `tsp_solver.zpl` en remplaçant `"tsp-xx.txt"` par le nom du fichier de test souhaité, par exemple : `tsp5.txt`, `tsp25.txt`, `tsp50.txt`, ou `tsp101.txt`.

`set Villes := {read "tsp50.txt" as "<1n>" skip 1, <0>};`
`param coX[Villes] := read "tsp50.txt" as "<1n> 2n" skip 1, <0> 0;`
`param coY[Villes] := read "tsp50.txt" as "<1n> 3n" skip 1, <0> 0;`


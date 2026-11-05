# Erreur d'Euler par rapport à la solution échantillonnée

## Limite traitée
Le jalon précédent certifiait une application d'Euler et son suivi d'une cible instantanée. Il ne certifiait pas la proximité entre Euler et la dynamique continue. Ce jalon traite cette question pour le même modèle jouet, sous une hypothèse d'entrée précise : une valeur constante sur chaque intervalle du maillage, utilisée identiquement par les deux trajectoires.

## Hypothèses et objets comparés
Le champ normalisé est dx/ds=1−(1+v)x. Soit M≥0, un pas 0<τ≤1/(1+M), et une suite v(n)∈[0,M]. Le signal physique retenu vaut v(n) pour nτ≤s<(n+1)τ. Les changements d'entrée sont donc alignés sur le maillage.

L'itération d'Euler est X(n+1)=τ+[1−τ(1+v(n))]X(n). L'itération exacte échantillonnée est
Y(n+1)=f(v(n))+(Y(n)−f(v(n)))exp(−(1+v(n))τ), avec f(v)=1/(1+v).

La formule analytique du jalon précédent satisfait la condition initiale et l'équation différentielle sur chaque intervalle à entrée constante. Y est ici sa composition aux instants de grille. Il ne s'agit pas de remplacer une entrée arbitrairement variable par sa valeur courante dans une formule à entrée constante.

Les états initiaux physiques appartiennent à [0,1]. Le théorème d'erreur autorise un état Euler initial différent ; la variante à départ commun est la lecture la plus simple. Si les deux départs sont physiques, les deux trajectoires le restent.

## Borne locale puis globale
Pour z≥0, 0≤exp(−z)−1+z≤z²/2. Pour un état physique x et 0≤v≤M, cela donne le défaut non normalisé sur un pas :
|Eτ(v,x)−sample(τ,v,x)|≤τ²(1+M)²/2.

Sous le pas choisi, la pente Euler est comprise entre 0 et 1−τ. Avec e(n)=|X(n)−Y(n)| et D=τ²(1+M)²/2, on obtient e(n+1)≤(1−τ)e(n)+D. La somme géométrique donne

e(n)≤(1−τ)^n e(0)+[τ(1+M)²/2]·[1−(1−τ)^n].

À départ identique, e(0)=0, donc e(n)≤τ(1+M)²/2 pour tout n. C'est une borne O(τ), uniforme sur les instants de grille et en horizon, pour cette classe contractante. Elle est conservative, pas optimale. La borne peut être peu informative à gros pas ; elle ne remplace pas le choix d'une tolérance utile.

Le pas imposé ici est plus restrictif que la seule préservation physique prouvée précédemment. Par exemple, M=3 autorise physiquement τ=1/3, mais le théorème présent suppose τ≤1/4. Ne pas interpréter cette restriction suffisante comme un seuil nécessaire de convergence ou d'admissibilité.

En temps physique, τ=k_off h. Pour la fraction libre, la contribution uniforme s'écrit h(k_off+k_on L_max)²/(2k_off). Une erreur de concentration libre se déduit en multipliant par R_total. Aucune valeur de ces paramètres n'est ajustée sur des observations.

## Comparaison à la littérature
La démarche est classique : défaut local d'ordre deux, propagation par stabilité et erreur globale d'ordre un. Certaines références définissent l'erreur de troncature locale après division par le pas et lui donnent donc l'ordre un pour Euler. Notre « défaut local » est explicitement non normalisé.

La borne générique de Lipschitz peut croître avec l'horizon ; le facteur contractant particulier 1−τ fournit ici une somme géométrique bornée uniformément. La constante ci-dessus est démontrée pour ce modèle, pas attribuée aux références comme si elles la donnaient. Aucune nouveauté scientifique n'est revendiquée. SOURCES_FR.md identifie les pages directement lues.

## Tests indépendants des preuves
Les tests utilisent des encadrements rationnels de exp(−z) pour 0≤z≤1, via les sommes alternées de degrés 20 et 21. Toutes les comparaisons aux bornes sont faites sur les extrémités en Fraction, pas sur des nombres flottants. L'algorithme d'encadrement lui-même n'est pas formalisé en Lean.

Le benchmark comprend 572 configurations locales, puis deux signaux sur l'horizon normalisé 1 et six maillages, de τ=1/4 à τ=1/128. Les commutations du second signal restent à 1/4,1/2,3/4 pour tous les maillages : on compare bien la même entrée, pas une famille de signaux différents. Les nombres décimaux affichés sont des approximations de présentation. Trois cas complémentaires couvrent M=0 avec τ=1, des états initiaux distincts (dont un état Euler hors de [0,1]) et un horizon nul. Ces tests finis ne remplacent pas les théorèmes.

## Ce qui reste hors portée
- Erreur entre points de grille ou d'un interpolant Euler.
- Entrée continûment variable à l'intérieur d'une maille, et erreur liée à son maintien constant approximatif.
- Erreurs d'arrondi en virgule flottante, incertitude des paramètres, erreurs de mesure ou défaut d'adéquation du modèle.
- Réseaux réactionnels généraux, déplétion non modélisée du ligand, équivalence générale de trajectoires CRN et validation biologique.

Le résultat concerne les récurrences Euler/exacte échantillonnée déclarées. La formule analytique de chaque segment est vérifiée séparément ; cela n'est pas une nouvelle formalisation générale de la théorie des ODE ou de leur unicité. Le script original complet a été reconstruit indépendamment avec succès sous Lean 4.34.1. Les 21 déclarations auditées dépendent seulement de propext, Classical.choice et Quot.sound ; les tests passent. Les interfaces de segments formalisent également leurs conditions initiales, dérivées et jonctions de valeurs. Il s’agit des dérivées de chaque prolongement à entrée constante, pas d’une dérivée globale aux sauts. Aucun objet global assemblé ni son unicité ne sont formalisés ici.

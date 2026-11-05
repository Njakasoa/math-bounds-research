# Sources vérifiées : erreur d’Euler explicite

Consultation : 5 novembre 2026. Il s’agit d’un modèle mathématique jouet,
`x′ = 1 − (1 + v)x`, sans validation biologique. Les références établissent
des principes classiques ; aucune n’est présentée comme la source de notre
constante particulière ou comme une preuve de nouveauté.

## 1. Défaut local, convergence et propagation des erreurs

Tobin A. Driscoll et Richard J. Braun, *Fundamentals of Numerical Computation*,
édition en ligne, §6.2 « Euler’s method » :
<https://fncbook.com/julia/euler/>.

**Accès effectivement obtenu :** page HTML publique ouverte, équations et
preuve du théorème 6.2.1 lues, pas seulement un extrait de moteur de recherche.
Les auteurs sont identifiés sur <https://fncbook.com/>.

**Énoncés vérifiés :** l’équation (6.2.6) donne le défaut d’un pas démarré sur
la solution exacte : `h²u″(t_i)/2 + O(h³)`. Le théorème 6.2.1 suppose un
défaut normalisé borné par `Ch^p` et `|∂φ/∂u| ≤ L`, avec donnée initiale
exacte, puis conclut à une erreur globale au plus
`Ch^p (exp(L(t_i−a))−1)/L`. La preuve propage les défauts
par une récurrence et une somme géométrique, équations (6.2.13)–(6.2.17).
Pour Euler, cela donne l’ordre global un sur intervalle de temps fixé.

**Attention de vocabulaire :** cette référence appelle « LTE » le défaut
divisé par `h`, donc `O(h)` pour Euler. Notre « défaut local O(h²) » est le
défaut **non normalisé**. Sa borne générale ne garantit pas une erreur
uniforme lorsque le temps tend vers l’infini.

## 2. Facteur de propagation d’Euler et stabilité

Driscoll et Braun, même ouvrage, §11.3 « Absolute stability », exemple 11.3.1 :
<https://fncbook.com/python/absstab-diffusion/>.

**Accès effectivement obtenu :** page HTML publique ouverte ; définition
11.3.1 et équations (11.3.5)–(11.3.7) lues directement.

**Énoncés vérifiés :** pour `y′ = λy`, Euler donne
`y_(k+1) = (1 + hλ)y_k`. La stabilité absolue, définie ici comme le caractère
borné de la suite à pas fixé, équivaut à `|1 + hλ| ≤ 1`.

**Lien avec notre calcul, non énoncé par cette source :** sur chaque maille,
la différence entre deux mises à jour affines de notre modèle est multipliée
par `1 − h(1 + v_n)`. Sous `0 ≤ v_n ≤ M` et `0 < h ≤ 1/(1+M)`, ce facteur
est compris entre `0` et `1−h`. Cette condition assure une contraction et
préserve `[0,1]` ; elle est plus restrictive que la simple stabilité absolue.
La somme géométrique contractante explique la borne uniforme en temps.

## 3. Discontinuités : périmètre d’application

Lawrence Livermore National Laboratory, documentation officielle SUNDIALS,
« Usage Notes », section « On controlling unphysical solutions and
integrating over discontinuities », parties A2 et B2 :
<https://computing.llnl.gov/projects/sundials/usage-notes>.

**Accès effectivement obtenu :** page HTML publique ouverte ; les explications
et les étapes du traitement des discontinuités ont été lues directement.

**Énoncés vérifiés :** les discontinuités du second membre exigent un
traitement adapté aux hypothèses de régularité des intégrateurs. Pour des
sauts importants, la documentation préconise d’atteindre la discontinuité,
d’appliquer le changement de modèle et de redémarrer. Elle distingue aussi
l’erreur de modélisation de l’erreur de résolution numérique.

**Limite de cette référence :** c’est une recommandation d’implémentation
SUNDIALS, pas un théorème d’erreur d’Euler pour notre entrée discontinue.

## Portée exacte de la comparaison proposée

Les deux trajectoires doivent utiliser **la même entrée**
`v(t)=v_n` sur chaque intervalle `[nh,(n+1)h)`, avec `0≤v_n≤M`.
La solution exacte est continue et lisse à l’intérieur de chaque maille ;
on applique le calcul de défaut maille par maille, sans supposer une dérivée
seconde globale aux instants de commutation. Les valeurs au départ de chaque
pas utilisent l’entrée du nouvel intervalle.

Avec les deux états initiaux dans `[0,1]` et `0<h≤1/(1+M)`, le calcul propre
au modèle combine un défaut `≤h²(1+M)²/2` et une contraction `≤1−h` pour obtenir

`|x_n−x(nh)| ≤ (1−h)^n |x_0−x(0)| + h(1+M)² [1−(1−h)^n]/2`.

À `n=0`, le facteur de propagation vaut 1, y compris lorsque `h=1`.
Il s’agit d’une application élémentaire « consistance + stabilité » ; la
constante affichée doit être démontrée dans le présent travail, non attribuée
aux sources. Le résultat ne borne ni l’erreur consistant à remplacer une
entrée quelconque par son échantillonnage, ni les arrondis numériques, ni
l’écart entre le modèle jouet et un système biologique réel.

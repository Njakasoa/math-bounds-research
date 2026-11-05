# Un certificat Bernstein pour une réalisation globale scalaire

## Résultat vérifié et motivation
L'étape précédente construisait un atlas de certificats locaux. Ici, un exemple est réalisé par une seule application polynomiale et un seul état, sans changement de cellule. Il s'agit d'une adaptation de méthodes classiques de Bernstein et de relaxation scalaire, sans revendication de nouveauté.

Pour u dans [-1,1], poser S(u)=1+4u² et
G(u,x)=5/13 + (1−(5/13)S(u))x.
Les preuves Lean établissent que G préserve [-5,5], est uniformément contractante avec facteur certifié 12/13 et a pour unique point fixe 1/S(u). Un polynôme R(u) en sortie donne R(u)/S(u) à l'équilibre.

Avec t=(u+1)/2, les coefficients Bernstein de degré 5 de S sont [5,9/5,1/5,1/5,9/5,5]. Ceux de 1−(5/13)S sont [−12/13,4/13,12/13,12/13,4/13,−12/13]. Leur enveloppe convexe fournit la borne réelle.

## Ce que vérifie le nouveau checker
BernsteinCertificate.check est un calcul booléen sur des rationnels : rayon non négatif, 0≤κ<1, chaque coefficient de module au plus κ, et |η|+κr≤r. Sa correction, combinée aux lemmes GlobalScalarMap, prouve invariance et contraction pour l'application affine d'état associée. L'identité entre son polynôme et la cible S doit être prouvée séparément ; elle l'est pour cet exemple. Un test modifiant η seul passe donc légitimement le checker de bornes, mais ne certifie plus la même cible.

L'encodage monomial explicite de cette même application a une borne syntaxique de Lipschitz 28/13 dans l'ancien checker, qui le rejette pour tous les rayons et facteurs proposés. Cela ne montre pas que toutes les autres réalisations ou réécritures sont impossibles, ni que le nouveau checker englobe toute l'ancienne classe multivariée.

## Entrée variable et limite démontrée
Pour toute suite d'entrées admissibles et tout état initial dans la boîte commune, la trajectoire reste dans cette boîte. Deux trajectoires soumises à la même suite se rapprochent au plus comme (12/13)^n fois leur écart initial. Pour une entrée constante, la même borne contrôle l'erreur vers 1/S(u).

Cela ne donne pas le suivi exact d'un équilibre instantané mobile. Pour les entrées alternées 0,1, la trajectoire 1/53,21/53,1/53,… est exacte. À chaque temps pair, son erreur à l'équilibre courant vaut 52/53. Le contre-exemple et son identification avec la récurrence sont formalisés.

## Portée de l'optimalité
Le théorème classique de relaxation scalaire pour une enveloppe positive [l,H] donne η=2/(l+H), κ=(H−l)/(H+l), rayon 1/l. Le choix 5/13 et le facteur 12/13 sont optimaux seulement pour l'enveloppe de coefficients Bernstein de degré 5 fixée [1/5,5]. Ils ne sont pas optimaux sur la vraie plage S∈[1,5] : celle-ci autorise η=1/3, κ=2/3 et rayon 1. Avec les coefficients Bernstein de degré 5, η=1/3 obtient seulement la borne certifiée 14/15 et le rayon 5.

## Limites
- Pas de théorème général de complétude ou de synthèse Bernstein pour toute cible.
- Pas d'extraction algorithmique de toutes les constructions réelles : des définitions sémantiques sont noncomputables. Le checker rationnel est exécutable.
- Les 39 identités d'élévation de degré n=2,…,40 sont des tests rationnels exacts Python, pas un théorème Lean universel de degré minimal.
- Aucun résultat de temps continu, d'application biologique ou sur AK.
- Le cache Mathlib est réutilisé, et non reconstruit entièrement depuis ses sources.

## Antécédents
- Mathlib, polynômes de Bernstein : dépendance épinglée dans verification/environment.json.
- Richardson, relaxation optimale classique : https://jschoeberl.github.io/iFEM/iterative/Richardson.html (section 74.1).
- T. Hamadneh, thèse 2018, Bounding Polynomials and Rational Functions in the Tensorial and Simplicial Bernstein Forms : https://d-nb.info/1151075027/34.
- Diniz, Salasar et Stern, Positive Polynomials on closed boxes : https://arxiv.org/abs/1610.01437v2.

## Provenance
Les trois modules historiques inchangés viennent du dépôt https://github.com/Njakasoa/math-bounds-research au commit adda7cacf9e98164b2ff5fb1bec47108cdea027a. Les sept autres modules constituent ce jalon local, soumis à reconstruction et revue indépendante avant publication. Le paquet semantic-corona manquant n'est pas présenté comme reconstitué.

# Borne de suivi sous variation contrôlée de l'entrée

Ce jalon distinct prolonge le contre-exemple du jalon Bernstein : une contraction commune ne suffit pas au suivi d'une cible qui change arbitrairement. L'hypothèse supplémentaire est maintenant quantitative et explicite.

Pour la même récurrence x(n+1)=5/13+(1−(5/13)(1+4u(n)²))x(n), avec u(n) dans [-1,1], poser f(u)=1/(1+4u²) et e(n)=|x(n)−f(u(n))|. Une borne Lipschitz globale commode est |f(u)−f(v)|≤2|u−v|. La constante 2 n'est pas présentée comme optimale.

L'inégalité élémentaire de suivi formalisée est e(n+1)≤(12/13)e(n)+2|u(n+1)−u(n)|. Elle conserve le décalage d'indexation : la mise à jour utilise u(n), tandis que l'erreur suivante est mesurée à la cible f(u(n+1)).

Son déroulement donne une convolution finie des variations passées, pondérées géométriquement. Si |u(n+1)−u(n)|≤δ pour tout n, il donne

e(n)≤(12/13)^n e(0)+26δ(1−(12/13)^n)≤(12/13)^n e(0)+26δ.

Il s'agit de perturbation classique d'une récurrence contractante, sans revendication de nouveauté. Ces constantes conservatrices ne démontrent aucune optimalité. Une petite variation d'entrée donne une petite contribution forcée à l'erreur, après décroissance du transitoire initial. Une variation seulement bornée et non nulle ne garantit pas une erreur tendant vers zéro. Le cycle alterné antérieur reste compatible avec la borne, mais celle-ci y est peu informative.

La borne d'erreur est valable pour tout état initial réel puisque l'application affine considérée est globalement contractante en l'état. L'invariance de la boîte [-5,5], résultat distinct du jalon précédent, exige que l'état initial y appartienne.

Les expériences Python utilisent exclusivement Fraction pour les assertions : entrée constante, rampe de pas 1/100, cycle alterné, entrée non monotone. Les erreurs affichées en décimales sont des approximations de présentation, pas des preuves. Sur la rampe de 50 pas partant à l'équilibre, l'erreur maximale observée est environ 0,027 ; la borne uniforme forcée est 0,26. Aucun balayage fini ne constitue une validation universelle.

Les trois nouveaux modules ont compilé sous Lean 4.34.1. La revue indépendante et la reconstruction isolée complète du script original ont réussi. L’audit du paquet contrôle 21 déclarations nommées ; un audit indépendant supplémentaire contrôle convolution_zero. Les 22 théorèmes/lemmes ne dépendent que de propext, Classical.choice et Quot.sound. Aucun résultat de temps continu, de convergence pour toute entrée variable ou d'application biologique n'est déduit.

Les quatre modules Bernstein importés sont inchangés par rapport au jalon publié : https://github.com/Njakasoa/math-bounds-research/tree/e42783a630fd4f1a970fed9bc24bdb67806f5c9a/jalons/bernstein-global-20261105. Le nouveau code est dans ReciprocalVariation.lean, TrackingRecurrence.lean et BernsteinTracking.lean.

# Revue indépendante du jalon Bernstein

5 novembre 2026. Revue mathématique abstraite ; aucune source de l’auteur modifiée.

## Lecture des énoncés

Le checker rationnel Bernstein vérifie uniquement un rayon non négatif, un taux entre 0 et 1 strictement, la borne absolue de chaque coefficient Bernstein et le budget |η|+κr≤r. Sa validité repose sur la positivité de la base sur [0,1] et sa somme égale à 1. Il ne vérifie pas à lui seul l’identité entre ces coefficients et une cible rationnelle. Cette obligation est correctement séparée et prouvée pour l’exemple par des identités polynomiales exactes.

Pour t=(u+1)/2, S=5−16t+16t²=1+4u². Les coefficients de S dans la base Bernstein de degré 5 sont [5,9/5,1/5,1/5,9/5,5]. Avec η=5/13, les coefficients du résidu q=1−ηS sont [−12/13,4/13,12/13,12/13,4/13,−12/13]. Le checker accepte κ=12/13 et r=5.

Le système est exactement x(n+1)=5/13+(1−(5/13)(1+4u(n)²))x(n). Pour une entrée fixe u dans [−1,1], son unique équilibre réel est 1/(1+4u²). Le résultat de lecture polynomiale est également établi. Les dénominateurs non nuls sont déduits des hypothèses de contraction et non postulés sans justification.

## Comparaison avec l’ancien checker

Dans la coordonnée u initiale, la même pente vaut 8/13−(20/13)u². L’ancien encodage syntaxique calcule exactement la borne 28/13 et rejette cet AST pour tous rayon r et taux K. La nouvelle preuve obtient 12/13 avec la représentation Bernstein sur t∈[0,1]. Les deux identités d’évaluation établissent qu’il s’agit de la même mise à jour réelle.

Le rejet formalisé concerne cet encodage ancien explicite. Il ne faut pas l’étendre à toute réalisation ou à tous les checkers possibles. La preuve Bernstein est réelle sur le segment : elle ne prétend pas prolonger une contraction au disque complexe unité. Elle ne contredit donc pas les obstructions complexes du checker antérieur.

## Optimalité : restriction essentielle

Le choix η=5/13 et le taux 12/13 sont optimaux pour la borne obtenue à partir de l’enveloppe des coefficients de degré 5 fixée, [1/5,5]. Ce n’est pas l’optimum de la contraction réelle sur le segment. La vraie plage de S est [1,5] ; η=1/3 donne alors un taux réel 2/3 et un rayon invariant 1. Pour ce même η=1/3, l’enveloppe Bernstein de degré 5 donne seulement 14/15. La restriction est bien présente dans le théorème d’optimalité : il impose les deux contraintes aux extrêmes des coefficients 1/5 et 5.

La table Python des degrés 2 à 40 est une vérification finie de régressions, pas une preuve générale d’optimalité en degré, de complétude Bernstein ou de convergence de l’élévation de degré.

## Portée temporelle

Le résultat porte sur une récurrence discrète, pas sur une équation différentielle. Pour toute suite d’entrées admissibles :

- la boîte commune [−5,5] est invariante si l’état initial y appartient ;
- deux trajectoires soumises à la même suite d’entrées se rapprochent avec la borne (12/13)^n fois leur écart initial ;
- pour une entrée constante, l’erreur à la cible tend vers zéro avec la même borne géométrique.

Cela ne garantit pas de suivre une cible instantanée mobile sous entrées arbitraires, ni de converger vers un état constant. Le contre-exemple est exact : u alterne 0 et 1, et la trajectoire issue de 1/53 alterne 1/53 et 21/53. Aux temps pairs, l’erreur à 1/(1+4u²) est toujours 52/53. Il n’y a aucune contradiction avec la contraction synchronisée.

## Tests indépendants et limites

L’import et l’exécution de run() dans check_bernstein.py réussissent sans réécriture du fichier JSON de l’auteur. Identités rationnelles de degré 5, expansion indépendante SymPy, 39 élévations de degré, corruptions, 40 pas de trajectoires et cycle alterné passent. Le contrôle négatif avec une mauvaise valeur de η est particulièrement utile : le certificat de bornes peut passer alors que l’identité de cible échoue, ce qui confirme la nécessité de la preuve séparée.

La recherche dans les sept sources nouvelles de sorry/admit, axiomes ajoutés et contournements natifs est négative. Les détails définitifs de compilation et d’axiomes figurent dans le complément ci-dessous.

Aucune nouveauté mathématique, priorité de formalisation, complétude générale pour les réseaux multivariés, ou garantie de suivi temporel arbitraire n’est établie par ce jalon.

## Reconstruction isolée

Les journaux et empreintes de revue sont reproduits dans `verification/independent/`. Les chemins locaux ont été retirés des journaux distribués ; les originaux sont conservés séparément.

Le script indépendant de revue a reconstruit les dix modules historiques disponibles, puis les sept nouveaux modules, à partir de copies des sources et sans les anciens dossiers d’objets locaux dans LEAN_PATH. Il réutilise uniquement les objets mathlib/dépendances et le toolchain épinglé. Lean 4.34.1 ; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, comme lors de la revue précédente.

Un défaut réel a été trouvé dans le snapshot initial : `cycleState` utilisait une division réelle sans être déclaré noncomputable. L’auteur a corrigé cette seule déclaration, sans changer les preuves. Le fichier corrigé a ensuite été recompilé avec succès dans le dossier indépendant. Les sept sources finales correspondent exactement au snapshot de revue, comparaison et empreintes dans `source_comparison.json`. Les sept nouveaux modules et les dix anciens ont donc tous été reconstruits. Les diagnostics restants sont uniquement des avertissements de style tactique ou de dépréciation, sans trous de preuve.

Les logs conservent l’échec initial et la réussite finale. `SOURCE_SHA256SUMS` et `checksum_verification.txt` fixent l’intégrité du snapshot. L’audit indépendant porte sur treize déclarations clefs, transitivement, notamment la correction du checker, les identités de cible, la réalisation stationnaire, les garanties temporelles, le rejet de l’ancien checker, l’optimalité restreinte et le contre-exemple alterné.

**Résultat final de l’audit indépendant :** les treize déclarations dépendent uniquement de `propext`, `Classical.choice` et `Quot.sound`. Aucun `sorryAx`, aucune hypothèse axiomatique ajoutée ni contournement natif. Audit final et vérification des empreintes réussis. La correction noncomputable n’affecte pas le contenu mathématique des théorèmes, mais était nécessaire pour pouvoir annoncer honnêtement une compilation complète.

**Verdict :** accord sur ce jalon et sur sa portée précisément limitée. Cette revue ne recompile pas mathlib intégralement, n’audite pas le binaire Lean et ne démontre pas une nouveauté scientifique.

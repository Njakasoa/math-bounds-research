# Revue indépendante des preuves Lean de l’atlas

5 novembre 2026. Mathématiques abstraites exclusivement. Cette revue actualise le statut de la revue analytique antérieure : le compilateur Lean est maintenant disponible et a été exécuté.

## Verdict

Validation indépendante réussie pour `LocalAtlas.no_common_real_zero_iff_grid` et `LocalAtlas.exists_checked_grid`. Aucun défaut de preuve ou hypothèse cachée de certificat identifié. Vingt modules locaux/historiques reconstruits depuis leurs sources dans un dossier isolé, sans réutiliser leurs objets compilés originaux. Aucun diagnostic émis pour ces vingt compilations. Aucune source de l’auteur modifiée.

## Énoncés vérifiés

Pour toute dimension naturelle m et toute famille de k polynômes à coefficients rationnels, l’absence de zéro commun sur le cube réel fermé est équivalente à l’existence d’un N strictement positif pour lequel chacune des N^m cellules uniformes possède un certificat strict en norme des coefficients, avec un seul multiplicateur constant rationnel non nul au plus.

L’absence de zéro commun est définie par les évaluations réelles ordinaires, sans autre hypothèse. La norme est la somme des valeurs absolues des coefficients regroupés du polynôme, et non une norme syntaxique non simplifiée. La substitution affine est exactement u=c+v/N. La grille couvre les frontières incluses et le cas m=0. Pour une famille vide, l’hypothèse est impossible, plutôt que supposée vraie par vacuité : le cube contient toujours 0.

Le théorème de raccord construit existentiellement, sur chaque cellule, des multiplicateurs rationnels T, un système à un état accepté par le checker historique, et pour chaque entrée locale un unique état dans la boîte satisfaisant l’équation de point fixe et toutes les identités stationnaires de Bézout. Les sorties sont évaluées contre la famille initiale en coordonnées physiques c+v/N. L’acceptation n’est donc pas seulement un résidu borné abstrait sans rapport avec le checker.

## Reconstruction et axiomes

Dossier reproductible : `verification/independent/`.

- `rebuild.sh` copie les sources, reconstruit séquentiellement les dix modules historiques puis les dix modules nécessaires à l’atlas, avec `lean -j1`.
- `lean_path.txt` atteste que les dossiers contenant les anciens objets du checker et de l’atlas ont été retirés du chemin de recherche. Seuls les bibliothèques mathlib/dépendances, le toolchain et le dossier de revue y figurent.
- `SOURCE_SHA256SUMS` et `checksum_verification.txt` fixent les sources de la revue et vérifient leur intégrité.
- `IndependentAudit.lean` et `IndependentAudit.log` contiennent les énoncés développés et les axiomes transitifs.

Lean : 4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52.
Mathlib : commit d13f23b723b8a846827a245b89c10fc7d3f11612 ; son fichier lean-toolchain demande bien v4.34.1.

Les deux directions, leur équivalence, le théorème de raccord, la couverture, la majoration affine rationnelle et le raccord local ne dépendent que des axiomes usuels `propext`, `Classical.choice`, `Quot.sound`. Aucun `sorryAx`. La recherche des marqueurs sorry/admit, d’axiomes ajoutés et de contournements natifs dans les sources copiées est négative.

Empreintes des deux sources centrales, comparées identiques aux originales après reconstruction :

- LocalAtlasCompleteness.lean : 4f5d717873856b80d063a23d7d860879d1f694390a5f2c58238945b7a085f0fe
- LocalAtlasChecked.lean : 0134afd35c9ba39f6f331fb0e142c361543fff7d663c9785d119af6d18574c2c

## Limites exactes

1. La reconstruction isolée porte sur les vingt modules locaux/historiques utilisés. Les objets de mathlib et de ses dépendances ont été réutilisés depuis le cache restauré ; toute mathlib n’a pas été recompilée depuis ses sources. Ce n’est pas un audit du binaire Lean ni de la chaîne d’approvisionnement.
2. L’équivalence formalisée porte sur la grille uniforme à multiplicateurs constants. La troisième formulation du texte analytique, par couverture arbitraire de cubes rationnels avec multiplicateurs polynomiaux, n’est pas explicitement un énoncé de ces deux fichiers.
3. La construction d’existence et le constructeur de syntaxe canonique sont noncomputables. Le théorème prouve réellement que le checker accepte les objets existentiels, mais ne constitue pas une extraction Lean exécutable de l’algorithme complet de recherche d’atlas.
4. La preuve interne emploie la somme des constantes de variation et une marge issue de la somme des valeurs absolues divisée par k. Cela suffit à l’existence, sans formaliser exactement la meilleure borne avec maximum et marge optimale du texte analytique. Aucune complexité pratique ni optimalité quantitative générale n’est établie.
5. Le résultat de point fixe concerne les entrées locales fixes et l’unicité dans la boîte. Aucune stabilité sous commutation, aucune identité des solutions locales de Bézout sur les intersections, aucune réalisation globale unique n’est affirmée.
6. Cette reconstruction ne couvre pas les modules TwoCell* ni leur obstruction optionnelle, qui relèvent d’une vérification distincte. L’exemple rationnel avait été vérifié analytiquement et symboliquement dans la revue antérieure.
7. Aucune nouveauté mathématique ni priorité de formalisation n’est démontrée par cette revue.

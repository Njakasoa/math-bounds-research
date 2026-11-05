# Reproduction de la borne Euler–solution échantillonnée

Préparer le binaire Linux officiel Lean 4.34.1, Mathlib au commit d13f23b723b8a846827a245b89c10fc7d3f11612 et ses dépendances/caches épinglés (verification/environment.json et mathlib-lake-manifest.json). Le script ne télécharge ni n'installe rien.

Définir LEAN_BIN et MATHLIB_DIR comme chemins absolus, puis exécuter ./rebuild.sh. Le script contrôle le binaire et le commit, reconstruit les 7 modules dans build/ avec un chemin d'import isolé et exécute AuditEulerError.lean. Le cache Mathlib est réutilisé, non recompilé entièrement. Les 5 modules historiques sont inchangés depuis le dépôt https://github.com/Njakasoa/math-bounds-research au commit 7de40403e44d2099e5407a6689143a09381d47d2.

python verify_outputs.py contrôle les 21 déclarations nommées du nouveau code, y compris les lemmes annotés @[simp]. Seuls propext, Classical.choice et Quot.sound sont admis, sans obligation qu'une déclaration utilise les trois. Ce contrôle de journal ne remplace pas le noyau Lean.

python experiments/check_error.py exécute les tests et régénère error-results.json. La bibliothèque standard Python suffit. Les exponentielles sont encadrées par sommes alternées rationnelles ; les assertions utilisent Fraction et les décimales imprimées ne servent pas à accepter les tests. Cet algorithme d'encadrement n'est pas lui-même formalisé en Lean. Les preuves mathématiques sont distinctes.

Vérifier les empreintes distribuées avec sha256sum -c SHA256SUMS. Le manifeste est ajouté au conditionnement final, après insertion de la revue et des journaux. Les outils, caches et objets build/ ne sont pas inclus dans l'archive.

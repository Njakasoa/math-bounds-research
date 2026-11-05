# Reproduction

Préparer le binaire Linux officiel Lean 4.34.1 et Mathlib au commit d13f23b723b8a846827a245b89c10fc7d3f11612, avec ses dépendances et caches. Les identifiants exacts figurent dans verification/environment.json et mathlib-lake-manifest.json. Les caches et outils ne sont pas distribués.

Définir LEAN_BIN et MATHLIB_DIR comme chemins absolus correspondants, puis exécuter ./rebuild.sh. Le script ne télécharge ni n'installe rien. Il vérifie la version et l'empreinte du binaire, le commit Mathlib, reconstruit les 7 modules de modules.txt dans build/ avec un chemin d'import isolé, puis exécute AuditTracking.lean.

Exécuter python verify_outputs.py pour contrôler les audits de 21 déclarations nommées (liste non exhaustive) : seuls propext, Classical.choice et Quot.sound sont admis par cette vérification. Il ne remplace pas le noyau Lean. Exécuter python experiments/check_tracking.py pour les tests rationnels exacts. Ceux-ci utilisent uniquement la bibliothèque standard Python et régénèrent tracking-results.json.

Les avertissements de style de tactique, s'il y en a, ne sont pas des trous de preuve. Le cache Mathlib est réutilisé, pas recompilé intégralement. Vérifier les fichiers distribués avec sha256sum -c SHA256SUMS. Les objets build/ ne sont pas inclus dans l'archive.

Un 22e lemme, TrackingRecurrence.convolution_zero, est contrôlé séparément dans verification/IndependentSupplement.lean ; le résultat est dans independent-supplement.log. Après rebuild.sh, on peut refaire ce contrôle avec le même LEAN_PATH isolé et lean verification/IndependentSupplement.lean. La revue a exécuté le script original complet sans modification, avec succès.

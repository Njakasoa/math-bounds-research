# Reproduire le jalon Bernstein

Préparer Lean 4.34.1 officiel et Mathlib au commit d13f23b723b8a846827a245b89c10fc7d3f11612, avec les dépendances épinglées dans verification/mathlib-lake-manifest.json et les caches officiels nécessaires. Aucun téléchargement ni installation n'est réalisé par rebuild.sh. La restauration des dépendances est extérieure au paquet.

Définir LEAN_BIN comme chemin absolu du binaire lean et MATHLIB_DIR comme chemin absolu du checkout Mathlib, puis exécuter ./rebuild.sh. Le script contrôle le commit Mathlib, la version, le commit et l'empreinte du binaire Linux Lean ; construit les 10 modules de modules.txt dans build/ ; exécute l'audit d'axiomes et les sondes booléennes. LEAN_PATH est reconstruit avec les seules dépendances Mathlib et ce build, sans les anciens modules du laboratoire. Les diagnostics sont conservés dans verification/rebuild/.

Les sondes booléennes doivent afficher, dans l'ordre : true, true, false, false, false, false, true. Le dernier true est intentionnel : une vérification de bornes n'est pas une vérification de l'identité cible.

Pour les expériences séparées, utiliser Python et SymPy 1.14.0, puis python experiments/check_bernstein.py. Les calculs sont rationnels exacts ; ils ne remplacent pas les preuves Lean. L'exécution régénère experiments/experiment-results.json.

Les empreintes distribuées se vérifient par sha256sum -c SHA256SUMS. Les binaires compilés et caches volumineux ne sont pas inclus. Lire RESULTAT_FORMEL_FR.md pour les limites scientifiques et le rapport de revue pour le périmètre exact de validation.

Après reconstruction, python verify_outputs.py contrôle les 63 audits nommés (axiomes admis pour cet audit : propext, Classical.choice et Quot.sound) et la séquence exacte des sept sondes booléennes. Il produit verification/FINAL_VALIDATION.json. Il ne remplace pas le contrôle du noyau Lean.

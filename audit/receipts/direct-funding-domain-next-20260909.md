# Prochain pont de financement — revue bornée, sans modification des preuves

Statut : argument arithmétique très largement suffisant identifié ; **plafond protocolaire non encore prouvé**. Aucun build lancé. Revue des sources locales épinglées et des références primaires immuables ci-dessous. Les calculs JSON/Python sont des observations reproductibles, pas des théorèmes Lean ni une validation du trie de genesis.

## Proposition minimale

Garder un compteur abstrait de **crédits externes à la couche d'exécution**, puis prouver que la somme naturelle des balances EVM ne dépasse jamais l'allocation initiale plus ces crédits. Il suffit de majorer grossièrement les crédits ; aucune modélisation de l'inflation réelle, du rendement des validateurs ou du prix de l'ETH n'est nécessaire. En particulier, compter chaque retrait CL→EL comme une nouvelle émission EL reste une surestimation correcte, même lorsqu'il restitue un dépôt déjà compté auparavant.

Le domaine à annoncer serait : une branche valide issue d'une genesis identifiée, suivie selon une séquence de forks explicitement sélectionnée ; nombres de blocs/slots et retraits liés aux règles CL/EL correspondantes ; appels ordinaires réellement admis et financés. Cela ne couvre pas toutes les valeurs possibles des paramètres bruts de Θ/Υ, une genesis arbitraire, des crédits arbitraires par un harnais de test, ni des modifications futures de protocole non sélectionnées.

## Quantités et majorant proposé

Le `FundedDomain.fundingCeiling` actuel vaut exactement :

```
76059800903738432429721259523001950250726052916847211303159755524395288041 wei
```

Soit environ 7,606×10^73 wei. Il s'agit de la quote certifiée au numérateur 2892, strictement exclue pour les valeurs admises dans le lemme de préservation. Le type UInt256 de value seul ne donne pas cette borne.

La lecture entière du fichier d'allocation mainnet de la référence EL donne 8 893 entrées, totalisant **72 009 990 499 480 000 000 000 000 wei**, donc moins de 2^96. Le plus gros compte contient 11 901 484 239 480 000 000 000 000 wei. Le fichier n'est utilisé ici que pour l'allocation ; son ancien objet config ne sélectionne pas notre calendrier de forks. Il reste à lier cette allocation à la genesis normative et au monde Lean utilisé. [Allocation mainnet immuable](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/assets/mainnet.json), [chargement de genesis](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/genesis.py).

Sous les obligations de domaine détaillées ensuite, prendre :

```
I = 2^96
  + 2^64 × (16 × 10^18)
  + 2^64 × 16 × 2^64 × 10^9
  = 5444517871030163320672574707278555720889543950336 wei
  < 2^163
  < fundingCeiling.
```

Les trois termes sont l'allocation initiale, une surestimation des récompenses PoW, et une surestimation de tous les retraits. On peut conserver **2^200** comme interface de preuve confortable : I < 2^200 < fundingCeiling < 2^256. Aucun besoin de calculer la supply actuelle.

Si l'on préfère éviter de figer le nombre 16 à l'interface, une borne beaucoup plus faible « moins de 2^64 retraits par payload » suffit aussi : remplacer ce 16 par 2^64 donne moins de 2^223, encore inférieur à fundingCeiling. Cette variante utilise un plafond de financement 2^223 et exige toujours une justification du domaine ; elle ne permet pas de conclure 2^200.

## Quelles règles créent réellement des balances EL ?

1. **Genesis** installe directement les balances de l'allocation. Ce n'est pas une transaction ordinaire, et les restrictions sur les transactions ne bornent pas une genesis libre.
2. **Récompenses PoW avant Paris** : Frontier fixe 5 ETH de base ; au maximum deux ommers sont admis, chacun d'âge valide. La prime du mineur est la base plus base/32 par ommer ; la récompense d'ommer ne dépasse pas la base. Donc moins de 16 ETH par bloc est un majorant simple, incluant les deux ommers. [Frontier](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/frontier/fork.py).
   Les constantes inspectées passent à 3 ETH dans Byzantium puis 2 ETH dans Constantinople. Paris n'appelle plus pay_rewards et impose l'absence d'ommers. Ceci étaye le majorant ; la preuve de la chaîne complète des forks et de leurs transitions irrégulières reste à fournir. [Byzantium](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/byzantium/fork.py), [Constantinople](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/constantinople/fork.py), [Paris](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/paris/fork.py).
3. **Retraits** : le process_withdrawals EL archivé crédite chaque adresse de amount×10^9 wei. Dans les types CL, amount est Gwei/Uint64 ; Withdrawals est une liste bornée, Capella fixe son plafond à 16. Le type Withdrawal local d'EVMYulLean a aussi amount : UInt64, mais ce type seul ne prouve ni la taille de la liste ni le traitement des blocs. [Traitement EL archivé](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/amsterdam/fork.py), [types et plafond Capella](https://github.com/ethereum/consensus-specs/blob/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/capella/beacon-chain.md).
4. Les crédits de remboursement de gas et de rémunération du bénéficiaire sont des **restitutions/transferts de fonds préalablement débités**, sous validité et absence de sous-flux. Leur fonction EL peut s'appeler create_ether : ce nom ne suffit pas pour les classer comme émission nette. Les tips, CALL, CREATE et SELFDESTRUCT ne doivent pas augmenter le total net ; les burns, les suppressions et les fonds immobilisés peuvent être ignorés pour une borne supérieure.
5. Les récompenses CL deviennent dépensables dans l'EL via les retraits : inutile d'ajouter séparément toutes les récompenses CL. Les nouveaux retraits de builders dans le Gloas archivé doivent rester inclus dans la même liste bornée et dans le comptage des payloads. Une transition spéciale de fork qui changerait des balances réclame une preuve dédiée. Le module DAO inspecté appelle apply_dao ; son corps n'a pas été inspecté ici et aucune conservation de cette migration n'est revendiquée. [Point d'appel DAO](https://github.com/ethereum/execution-specs/blob/0cc100eb190b64b23baba72dac0165652eaec252/src/ethereum/forks/dao_fork/fork.py), [Gloas archivé](https://github.com/ethereum/consensus-specs/blob/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/gloas/beacon-chain.md).

## Champs bornés et portée temporelle

L'histoire post-merge peut être bornée par les slots distincts, chacun Uint64, avec au plus un payload crédité par slot. Une branche peut contenir des slots vides ; cela ne nuit pas à la borne. Les traitements différés Gloas doivent créditer le payload une seule fois. Il faut transporter la propriété de la transition CL réelle vers les événements EL, pas simplement compter des appels de test. [Phase0 archivé](https://github.com/ethereum/consensus-specs/blob/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/phase0/beacon-chain.md), [Gloas archivé](https://github.com/ethereum/consensus-specs/blob/ad0058fd0d34c5dcf504fa51ea2f4f11077b9996/specs/gloas/beacon-chain.md).

Pour le pré-merge, ne pas déduire une borne PoW des slots beacon. Le pont proposé est différent : les hauteurs EL augmentent de un depuis genesis et le payload final sélectionné porte un block_number Uint64. Toute son ascendance canonique, donc ses blocs PoW, a moins de 2^64 hauteurs. Les références Frontier et Paris inspectées vérifient number=parent.number+1 ; le maintien de ce lien dans tous les forks reste une obligation. Aucun chiffre historique de hauteur du Merge n'est nécessaire pour cet argument. Capella et Gloas exposent le champ borné du payload ; les champs Nat du BlockHeader Lean ne le garantissent pas eux-mêmes.

Le retrait possède aussi un WithdrawalIndex Uint64 global. Une preuve de monotonie/non-répétition pourrait donner un autre majorant cumulatif sans compter les slots. Ce n'est pas le plus petit travail : le traitement Gloas et les conversions/overflow doivent encore être liés. La borne par slot et longueur de liste réutilise mieux ResourceBounds.

## Pont manquant dans le vrai évaluateur Lean

Source épinglée : EVMYulLean b62586650b4f96cc6da25f36574aaa8f329a6420.

- **Υ, lignes 832–953** : l'admission est annoncée dans un commentaire, pas implémentée ici. Le débit gasLimit×p et le blob fee utilisent des mots ; un appel brut invalide peut sous-fluer. Il faut une précondition de validité sur les montants naturels calculés, qui implique debit+value≤balance avant le débit, p≥f, et le fit des conversions/produits. Ces propriétés ne se déduisent pas du seul type UInt256.
- **Θ, lignes 753–770** : crédite la cible puis débite le sender, sans vérifier elle-même les fonds. Un sender absent ou sous-financé n'est pas une transaction admissible par magie. Le lemme doit partir de fonds suffisants dans le vrai pré-monde. Le cas sender=target réclame le calcul de cette séquence exacte ; éviter une hypothèse d'absence d'alias inutile ou une substitution par transferBalance.
- **call/step, lignes 149–212 et 370–433** : le CALL interne vérifie value≤balance du codeOwner avant Θ. CALL transmet la même valeur apparente. CALLCODE a une autre cible de stockage, DELEGATECALL transfère zéro mais hérite d'une valeur apparente : les montants v/v' ne sont pas interchangeables. La garantie destinée aux prédeploys doit porter sur les appels à leur propre compte/code installé ; exécuter leurs octets par délégation ailleurs ne produit pas leur queue. Si l'on veut aussi couvrir ces contextes, une borne sur la valeur apparente doit être héritée de la vraie provenance du call stack, et non déduite de son transfert nul.
- **Lambda** : conservation sous financement, collision et rollback réels à traiter. Les cas où l'adresse calculée aliaserait le créateur demandent de conserver les vérifications de collision ; ne pas affirmer la conservation de chaque état artificiel de préparation sans inspection.
- **SELFDESTRUCT** : source EvmYul/Semantics.lean, lignes 395–475. Couvre transfert, zéro du source, et les deux comportements d'auto-cible. Les suppressions ultérieures réduisent le total ; ne pas les interpréter comme remboursement libre. Les autres opcodes ordinaires préservent les balances. Les précompiles et les erreurs/rollback nécessitent aussi leur cas dans l'induction.

Pour Υ, utiliser un petit invariant de fonds réservés : worldSum + escrow ≤ budget. Le débit initial retire g×p et les blob fees ; les remboursements et tips satisfont en Nat

```
gStar*p + (g-gStar)*f ≤ g*p   si 0≤gStar≤g et f≤p.
```

`RefundAccounting` fournit déjà gStar≤g sous la borne du vrai gaz restant. Les fits des produits monétaires viennent de l'admission et du budget initial, pas d'une égalité postulée sur le monde final. Ce mécanisme couvre les transactions échouées aussi. La preuve d'exécution doit conserver le budget au fil des frames et des rollbacks, y compris les appels finalement annulés par un ancêtre.

## Découpage formel conseillé

A. Arithmétique indépendante : somme des crédits sous les bornes ci-dessus ; I<2^200<fundingCeiling ; compte individuel≤somme du monde ; value≤balance<fundingCeiling. Un certificat fini de l'allocation peut servir de donnée initiale, avec parse/hash/identité explicitement séparés. Pas de nouvelle trace native_decide d'EVM.

B. Algèbre des balances : somme naturelle sur AccountMap, lois d'insert/erase, conservation de la séquence réelle de transfert avec sender=target et comptes absents, non-augmentation de SELFDESTRUCT. Ce sont des lemmes sémantiques génériques, pas une postcondition supposée dans un constructeur de Reachable.

C. Induction sur l'exécution et Υ : admission monétaire → opérations sans sous-flux → total monde/fonds réservés borné → appel réellement financé. Elle doit porter sur toutes les instructions capables de changer des balances dans les ancêtres, pas seulement le runtime EIP-8282.

D. Adaptateur du domaine : genesis normative, calendrier des forks, crédit PoW/retrait et indices réels, prédeploy/activation, et correspondance du modèle épinglé à ces règles. La référence Amsterdam comporte déjà un partage gas d'exécution/réservoir et des transactions SetCode que le Υ examiné n'a pas : la citer ne prouve pas sa correspondance avec le modèle. Les références restent des sources de règles, pas une migration implicite du pin.

Le chemin le plus court pour l'audit peut partir d'un **checkpoint d'activation identifié avec somme des balances certifiée**, puis ne prouver que la suite des forks retenus. Cela évite la conservation de chaque ancien fork ; en échange il faut une donnée initiale effectivement certifiée, pas simplement supposer le plafond au checkpoint. L'autre chemin part de genesis et assume plus de travail de correspondance historique. Le choix doit apparaître dans le domaine final du rapport.

À ce stade, il est exact de dire : « les règles de financement sélectionnées fournissent un majorant potentiel immensément inférieur au seuil ; les obligations de conservation/admission et de liaison au domaine restent ouvertes ». Il serait inexact de dire que `hvalue<fundingCeiling` est déjà une conséquence prouvée du protocole Ethereum.

## Reproductibilité

Nouveaux téléchargements : uniquement /tmp/eip-funding-sources, aux mêmes commits de référence déjà archivés. Métadonnées complètes : sources.json. Calculs : arithmetic.json. Aucun fichier du dépôt ni pin modifié. Les sources locales archivées initialement ont été lues depuis /tmp/eip-protocol-sources.

SHA-256 des fichiers sémantiques locaux inspectés :

- EvmYul/EVM/Semantics.lean : 8b49f1aee609ce888041ba9e7253bbe55d06fda136252bc46d4e006755110f4b
- EvmYul/Semantics.lean : e6bd5acd768d93f50a93f789a301d2f9218b210bdcd3739f95088fd4e5279d7b
- EvmYul/Maps/AccountMap.lean : 8ce51e59b0d2be13b7bb749225a28bb532c8cc07574f798617c03a7392b08b54

Nouvelles références téléchargées et hachées :

- `consensus-specs@ad0058fd0d34c5dcf504fa51ea2f4f11077b9996` / `specs/capella/beacon-chain.md` : `e68a7653e3bab44d4eae2a5b2e7b962605c166f8e9527c21e7a46a3ef8d63042`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/forks/frontier/fork.py` : `636a8111fa4a60bf793faaadc620715a75ec39ca4c9434db42bedf4236f6d138`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/genesis.py` : `e22eccebf3404e832245633ff88da4dc304ada33198fbf05d8bab50445af0e3c`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/assets/mainnet.json` : `48bb73806f4ed8f0e4f869cb0bc7ba2e1e5724ceb08c9ec079170dfd63042d65`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/forks/amsterdam/blocks.py` : `ec2cdd7fae64861b76c225573aac20be18ddb39e1fb2c2e0015a5cd0c4d2852c`
- `consensus-specs@ad0058fd0d34c5dcf504fa51ea2f4f11077b9996` / `specs/fulu/beacon-chain.md` : `0e72312417d1df6f7aac14f731bb6bd71a3ef2715ced68e0b039d7622abc4490`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/forks/byzantium/fork.py` : `6b593d3bb31b5ee8f2bf9f9745b2a90af24e28ccd716fd3bd012de8f407ce90b`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/forks/constantinople/fork.py` : `139b60c76f18068145d6d548b8e1f9228385fb145b4f6df942758ed0fa772efc`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/forks/paris/fork.py` : `2d87c6527d6e5e8d0ec5cfbe51da4e2ea39d7e6c6194ad5316b96d0b8789dacd`
- `execution-specs@0cc100eb190b64b23baba72dac0165652eaec252` / `src/ethereum/forks/dao_fork/fork.py` : `83d0dff4f9802f72791d206426cd29504b2a841eed9bd168e96b7c68c7addfa8`

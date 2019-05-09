---
title: "Experiments DeepSec"
pagetitle: "notes"
author: ""
header-includes:
   - \usepackage[english]{chetor_md}
fontsize: 11pt
---

-------

BAC
-------

* *2 sessions* **[violated]**
  - DeepSec vanilla: <1s (1 core), <1s (20 cores)
  - DeepSec session: <1s (1 core), <1s (20 cores)
  - DeepSec inclus.: <1s (1 core), <1s (20 cores)

* *3 sessions* **[violated]**
  - DeepSec vanilla: >24h (1 core), >24h (20 cores)
  - DeepSec session: 2s (1 core), 1s (20 cores)
  - DeepSec inclus.: 4s (1 core), <1s (20 cores)

* *4 sessions*
  + 3 identical passports + 1 fresh passport **[violated]**
    - DeepSec vanilla: >24h (1 core), >24h (20 cores)
    - DeepSec session: 2s (1 core), 1s (20 cores)
    - DeepSec inclus.: <1s (1 core), <1s (20 cores)
  + 2 identical passports + 2 fresh passports **[equivalent]**
    - DeepSec vanilla: >24h (1 core), >24h (20 cores)
    - DeepSec session: 128s (1 core), 14s (20 cores)
    - DeepSec inclus.: 86s (1 core), 12s (20 cores)

* *5 sessions*
  + 4 identical passports + 1 fresh passport **[violated]**
    - DeepSec vanilla: >24h (1 core), >24h (20 cores)
    - DeepSec session: 30s (1 core), 3s (20 cores)
    - DeepSec inclus.: 30s (1 core), 3s (20 cores)
  + 3 identical passports + 2 fresh passports **[violated]**
    - DeepSec vanilla: >24h (1 core), >24h (20 cores)
    - DeepSec session: SINCE 10:13AM (1 core), 2h47 (20 cores)
    - DeepSec inclus.: SINCE 10:13AM (1 core), ??? (20 cores)
  + 2 identical passports + 3 fresh passports **[???]**
    - DeepSec vanilla: >24h (1 core), >24h (20 cores)
    - DeepSec session: SINCE 10:13AM (1 core), SINCE 10:30AM (20 cores, 5000sets)
    - DeepSec inclus.: SINCE 10:13 (1 core), ??? (20 cores)

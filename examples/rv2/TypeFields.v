Definition instruction_type_fields (t : instruction_type) :=
  app (if has_opcode t then [opcode] else []) (
  app (if has_fct2   t then [fct2  ] else []) (
  app (if has_fct3   t then [fct3  ] else []) (
  app (if has_fct7   t then [fct7  ] else []) (
  app (if has_rs1    t then [rs1   ] else []) (
  app (if has_rs2    t then [rs2   ] else []) (
  app (if has_rs3    t then [rs3   ] else []) (
  app (if has_rd     t then [rd    ] else []) (
  app (if has_immI   t then [immI  ] else []) (
  app (if has_immS   t then [immS  ] else []) (
  app (if has_immB   t then [immB  ] else []) (
  app (if has_immU   t then [immU  ] else []) (
       if has_immJ   t then [immJ  ] else [])
  ))))))))))).


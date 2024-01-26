forbid(
  principal == a::"\0",
  action in [Action::"action"],
  resource
) when {
  (true && (({"\0>6\0\0\0": []}["\0>6\0\0\0"]) == ({"\0>6\0\0\0": []}["\0>6\0\0\0"]))) && (!(principal has "\0>6\0\0\0"))
};

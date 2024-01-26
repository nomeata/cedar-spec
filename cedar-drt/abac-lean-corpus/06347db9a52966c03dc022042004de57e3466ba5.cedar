@A("")
forbid(
  principal in a::"G\0\u{10}",
  action in [Action::"action"],
  resource in a::"G\0\u{10}"
) when {
  true && (((A::"" == principal) == principal) == principal)
};

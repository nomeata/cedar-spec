permit(
  principal in a::"bbbbbbbbbbbbbbbbbbbbbbbb",
  action in [Action::"action"],
  resource is a in a::"bbbbbbbbbbbbbbbbbbbbbbbb"
) when {
  (true && (((a::"bbbbbbbbbbbbbbbbbbbbbbbb" in a::"bbbbbbbbbbbbbbbbbbbbbbbb") in (a::"bbbbbbbbbbbbbbbbbbbbbbbb" in a::"bbbbbbbbbbbbbbbbbbbbbbbb")) in ((Action::"action" == a::"bbbbbbbbbbbbbbbbbbbbbbbb") == principal))) && principal
};

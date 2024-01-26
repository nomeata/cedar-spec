@BiiisD("")
@t1("")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  false && (!(principal in action))
};

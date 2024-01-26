@B("action")
@J("")
forbid(
  principal,
  action in [Action::"action"],
  resource
) when {
  false
};

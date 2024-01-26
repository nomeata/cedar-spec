@B("a")
@J("")
@J30tk333("\0\0")
forbid(
  principal is a in a::"\0",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (a::"\0" in Action::"action")
};

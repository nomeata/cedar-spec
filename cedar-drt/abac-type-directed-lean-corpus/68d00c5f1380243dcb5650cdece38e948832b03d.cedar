@B("a")
@J("")
@J30tk333("\0")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  true && (principal has "")
};

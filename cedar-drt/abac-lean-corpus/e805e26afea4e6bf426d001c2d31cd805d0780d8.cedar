forbid(
  principal == a::"",
  action in [Action::"action"],
  resource is a in a::""
) when {
  ((true && ((("" in "") in a::"") in a::"")) && ((("" in "") in ("" in "")) in ((Action::"action" in "") in ("" in "")))) && ((("" in "") in ("" in "")) in ([true, A::""] in principal))
};

forbid(
  principal is a in a::"",
  action in [Action::"action"],
  resource
) when {
  (true && ({"_hhh": a::"" in a::""}.containsAll({"_hhh": principal}))) && principal
};

permit(
  principal is a in a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  ((true && (principal has "KAAAA")) && (a::"" has "KAAAA")) && (a::""["KAAAA"])
};

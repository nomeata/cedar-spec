permit(
  principal,
  action == Action::"action",
  resource is a in a::""
) when {
  true && (a::"j\0\0@" == ((context == context) == (Action::"action" == a::"")))
};

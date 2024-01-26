forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (((Action::"action" == a::"") == (a::"" has "")) == principal)) && false
};

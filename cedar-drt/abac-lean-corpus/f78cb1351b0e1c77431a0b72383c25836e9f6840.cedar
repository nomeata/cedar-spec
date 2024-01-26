forbid(
  principal == a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (((Action::"action" == a::"") == (a::"" has "")) == ((a::"" has "") has ""))) && (principal has "_hhh")
};

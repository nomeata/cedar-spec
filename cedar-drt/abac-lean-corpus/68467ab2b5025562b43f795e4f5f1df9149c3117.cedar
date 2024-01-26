forbid(
  principal in a::"",
  action == Action::"action",
  resource in a::""
) when {
  (true && (((Action::"action" == Action::"action") == (Action::"action" == Action::"action")) == ((Action::"action" == Action::"action") == principal))) && principal
};

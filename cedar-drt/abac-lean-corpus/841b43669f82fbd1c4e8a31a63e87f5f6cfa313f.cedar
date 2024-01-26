forbid(
  principal in a::"\0\0\0\0",
  action,
  resource in a::"\0\0\0\0"
) when {
  (true && context) && Action::"action"
};

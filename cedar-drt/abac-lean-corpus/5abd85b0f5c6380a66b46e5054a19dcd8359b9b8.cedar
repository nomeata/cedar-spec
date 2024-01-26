forbid(
  principal == a::"\0\0\0jj\0\0\0~",
  action,
  resource in a::"\0\0\0jj\0\0\0~"
) when {
  ((true && ((Action::"action" == (resource - a::"\0\0\0jj\0\0\0~")) == ((a::"\0\0\0jj\0\0\0~" == Action::"action") == (A0000::"jj\0\0\0\0" - a::"\0\0\0jj\0\0\0~")))) && a::"\0\0\0jj\0\0\0~") && (((a::"\0\0\0jj\0\0\0~" == Action::"action") == (resource - a::"\0\0\0jj\0\0\0~")) == ((a::"\0\0\0jj\0\0\0~" == Action::"action") == (principal - principal)))
};

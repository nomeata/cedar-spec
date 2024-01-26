@C("\0`")
permit(
  principal in a::"",
  action == Action::"action",
  resource == a::"llll\0`"
) when {
  (true && (action.greaterThan((!a::"") == a::"llll\0`"))) && false
};

permit(
  principal,
  action,
  resource is a in a::"hgj"
) when {
  ((true && Action::"action") && ((!true) in a::"hgj")) && principal
};

@r0("")
permit(
  principal,
  action,
  resource
) when {
  ((true && "") && Action::"action") && principal
};

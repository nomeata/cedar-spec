permit(
  principal,
  action,
  resource
) when {
  (true && (!({"A": principal}[""]))) && principal
};

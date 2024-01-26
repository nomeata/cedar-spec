permit(
  principal,
  action,
  resource == a::"jhjj"
) when {
  (true && (!(!action))) && principal
};

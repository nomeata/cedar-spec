permit(
  principal,
  action,
  resource
) when {
  (true && ({"o": principal}[""])) && principal
};

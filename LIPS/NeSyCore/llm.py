import re
import os
import warnings
from wrapt_timeout_decorator import timeout
from openai import OpenAI

from . import parser
from ..logger_config import default_logger, setup_logger


class LLM:
    def __init__(
        self,
        oai_version="gpt-4o",
        temperature=0.7,
        top_p=0.95,
        max_tokens=4096,
        logger=None
    ):
        self.oai_version = oai_version
        self.temperature = temperature
        self.top_p = top_p
        self.max_tokens = max_tokens
        self.idx = 0
        self.num_llms = 1
        # Setup logger if log_file is provided
        self.logger = logger or default_logger

    def set_api_key(self, idx=0):
        if idx == 0:
            client = OpenAI(api_key=os.getenv('OPENAI_API_KEY'))
        else:
            raise IndexError("No more API keys")
        return client

    def response(
        self,
        prompt: str,
        max_tokens: int = None,
        temperature: float = None,
        top_p: float = None,
        verbose: bool = False,
    ) -> str:
        """call the openai api to get the response

        Args:
            prompt (str): the prompt to generate the response
            max_tokens (int, optional): the max token length of the response. Defaults to None.
            temperature (float, optional): the temperature of the response. Defaults to None.
            top_p (float, optional): the top p of the response. Defaults to None.

        Returns:
            str: the response from the openai api
        """
        try:
            self.idx = self.idx // self.num_llms
            client = (
                self.set_api_key(self.idx // self.num_llms)
            )  # bad implementation, but no other ways to support multiprocess
        except Exception as e:
            self.logger.error(f"gpt-4 with index {self.idx} encounter an error {e}")
            warnings.warn(f"gpt-4 encounter an error {e}")
            return r"\\box{{0}}"
        max_tokens = max_tokens or self.max_tokens
        temperature = temperature or self.temperature
        top_p = top_p or self.top_p
        try:
            chat_completion = client.chat.completions.create(
                model=self.oai_version,
                messages=[{"role": "user", "content": f"{prompt}"}],
                temperature=temperature,
                max_tokens=max_tokens,
                top_p=top_p,
                frequency_penalty=0,
                presence_penalty=0,
                stop=None,
            )
            res = chat_completion.choices[0].message.content
        except Exception as e:
            self.logger.error(f"gpt-4 with index {self.idx} encounter an error {e}")
            raise RuntimeError("openai failed to response")
        if verbose == True:
            self.logger.debug(f"Prompt: {prompt}")
            self.logger.debug(f"Response: {res}")
        return res

    @timeout(30)
    def adaptive_response(self, prompt, fold=4):
        try:
            results = []
            for i in range(fold):
                response = self.response(
                    prompt, max_tokens=(i + 1) * (self.max_tokens // fold)
                )
                results = parser.extract_boxed_answers(response)
                if len(results) == 0 or ("".join(results) == ""):
                    self.logger.debug("llm response is empty, try again...")
                    continue
                else:
                    self.logger.debug(f"Prompt: {prompt}")
                    self.logger.debug(f"Response: {response}")
                    break
        except TimeoutError as e:
            self.logger.error(f"llm reponse timeout {e}")
            raise RuntimeError("openai adaptive response failed")
        return results

    def execute(self, proof):
        """
        Execute the calculation in Maple for all code blocks found in the input.
        """
        # Pattern to match both Maple and generic code blocks
        pattern = re.compile(r"```(maple)?(.*?)```", re.DOTALL)

        # Function to replace matched code blocks with their execution results
        def replace_with_result(match):
            maple_indicator, code_block = match.groups()
            if maple_indicator is not None:  # This is a Maple code block
                code_block = code_block.strip()
                res = self._exec(code_block)
                return res
            else:  # This is a generic code block, you might want to handle it differently
                return match.group(0)  # Return the whole match including the backticks

        # Replace all matched code blocks in the proof with their execution results
        proof = pattern.sub(replace_with_result, proof)
        return proof
